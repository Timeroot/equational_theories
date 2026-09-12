import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq521 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq621 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 y
       have i₂ := eq521 y X0
       grind)
    | (have i₁ := eq53 y
       have i₂ := eq521 y y
       grind)
    | exact superpose eq521 eq53
    | exact resolve eq53 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq521
  have eq747 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq12690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12690
    | exact resolve eq12690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12690
  have eq12702 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12691
       have r₂ := eq28
       grind)
    | exact resolve eq12691 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12691
  have eq12704 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12702
    | exact resolve eq12702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12702
  have eq12709 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq12704
  have eq12749 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12709
    | exact resolve eq12709 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12709
  have eq12857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12749 eq115
    | exact resolve eq115 eq12749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12749
  have eq12869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12857
  have eq12871 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12869
       have r₂ := eq28
       grind)
    | exact resolve eq12869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869
  have eq12877 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12871
  have eq12919 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12877
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12877
    | exact resolve eq12877 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12877
  have eq12946 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12919
       grind)
    | exact superpose eq12919 eq45
    | exact resolve eq45 eq12919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12919
  have eq12968 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12946
    | exact resolve eq12946 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946
  have eq13159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12968 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13159
    | exact resolve eq13159 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13159
  have eq13173 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13162
       have r₂ := eq28
       grind)
    | exact resolve eq13162 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13162
  have eq13175 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13173
    | exact resolve eq13173 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13173
  have eq13176 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13175
  have eq13182 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13176
  have eq13224 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13182
    | exact resolve eq13182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13182
  have eq13376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13224 eq12968
    | exact resolve eq12968 eq13224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12968 eq13224
  have eq13382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13376
  have eq13386 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13382
       have r₂ := eq28
       grind)
    | exact resolve eq13382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13382
  have eq13502 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13386 eq28
    | exact resolve eq28 eq13386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13504 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13386 eq76
    | (have r₁ := eq76
       have r₂ := eq13386
       grind)
    | exact resolve eq76 eq13386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq13386
  have eq13515 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13504
  have eq14097 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13515 eq115
    | exact resolve eq115 eq13515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14117 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq14097
  have eq14131 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14117
       have r₂ := eq13502
       grind)
    | exact resolve eq14117 eq13502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14117
  have eq14143 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq14131
  have eq14187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14143
    | exact resolve eq14143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14143
  have eq14286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14187 eq115
    | exact resolve eq115 eq14187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14187
  have eq14302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq14286
  have eq14306 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14302
       have r₂ := eq28
       grind)
    | exact resolve eq14302 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14302
  have eq14312 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq14306
  have eq14354 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14312
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14312
    | exact resolve eq14312 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14312
  have eq14382 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq14354
       grind)
    | exact superpose eq14354 eq45
    | exact resolve eq45 eq14354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354
  have eq14404 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq14382
    | exact resolve eq14382 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14382
  have eq14470 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14404 eq13515
    | exact resolve eq13515 eq14404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13515
  have eq14478 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14470
  have eq14486 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14478
       have r₂ := eq13502
       grind)
    | exact resolve eq14478 eq13502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13502 eq14478
  have eq14548 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14486
  have eq14592 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14548
    | exact resolve eq14548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14548
  have eq14706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14592 eq14404
    | exact resolve eq14404 eq14592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14404 eq14592
  have eq14712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14706
  have eq14720 : y = (M.op x y) := by
    first
    | (have r₁ := eq14712
       have r₂ := eq28
       grind)
    | exact resolve eq14712 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14712
  have eq14722 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq14720 eq21
    | exact resolve eq21 eq14720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq14728 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq14720 eq75
    | (have r₁ := eq75
       have r₂ := eq14720
       grind)
    | exact resolve eq75 eq14720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq14778 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) y) y) := by
    intro X0
    first
    | exact superpose eq14720 eq621
    | exact resolve eq621 eq14720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq14786 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq14728
  have eq14837 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14722
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14722
    | exact resolve eq14722 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14722
  have eq14839 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq14837 eq27
    | exact resolve eq27 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq17014 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq14786
       grind)
    | exact superpose eq14786 eq45
    | exact resolve eq45 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17028 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq747 x y
       have i₂ := eq14786
       grind)
    | exact superpose eq14786 eq747
    | (have j0 := eq747 x y
       grind)
    | exact resolve eq747 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14786
  have eq17031 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17028
  have eq17038 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17031
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17031
    | exact resolve eq17031 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17031
  have eq17050 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14837 eq17014
    | exact resolve eq17014 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17014
  have eq17052 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14837 eq17038
    | exact resolve eq17038 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17038
  have eq17064 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17050
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17050
    | exact resolve eq17050 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17050
  have eq17065 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17052
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17052
    | exact resolve eq17052 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17052
  have eq17073 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14837 eq17064
    | exact resolve eq17064 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17064
  have eq17074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14839 eq17065
    | exact resolve eq17065 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17065
  have eq17078 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17074
       have r₂ := eq28
       grind)
    | exact resolve eq17074 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17074
  have eq17082 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17078
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17078
    | exact resolve eq17078 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17078
  have eq17086 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14837 eq17082
    | exact resolve eq17082 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17082
  have eq17090 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17086
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17086
    | exact resolve eq17086 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086
  have eq17154 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq17090
  have eq17196 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14839 eq17154
    | exact resolve eq17154 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17154
  have eq17253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17196 eq17073
    | exact resolve eq17073 eq17196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17073 eq17196
  have eq17259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17253
  have eq17261 : x = (M.op y y) := by
    first
    | (have r₁ := eq17259
       have r₂ := eq28
       grind)
    | exact resolve eq17259 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17259
  have eq17280 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq14778 y
       have i₂ := eq17261
       grind)
    | exact superpose eq17261 eq14778
    | exact resolve eq14778 eq17261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14778
  have eq17283 : (M.op x y) = (k x y) := by grind
  have eq17325 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq17283
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17283
    | exact resolve eq17283 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17327 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq17280
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17280
    | exact resolve eq17280 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17280
  have eq17346 : y = (k x y) := by
    first
    | exact superpose eq14720 eq17325
    | exact resolve eq17325 eq14720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17325
  have eq17348 : y = (M.op y y) := by
    first
    | exact superpose eq14720 eq17327
    | exact resolve eq17327 eq14720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14720 eq17327
  have eq17359 : x = y := by
    first
    | (have i₁ := eq17348
       have i₂ := eq17261
       grind)
    | exact superpose eq17261 eq17348
    | exact resolve eq17348 eq17261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17261 eq17348
  have eq17368 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq25
    | exact resolve eq25 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq17507 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14837 eq17368
    | exact resolve eq17368 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837 eq17368
  have eq17566 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17507
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17507
    | exact resolve eq17507 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17507
  have eq17673 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17566 eq14839
    | exact resolve eq14839 eq17566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14839
  have eq17806 : x = (k x x) := by
    first
    | (have i₁ := eq17346
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq17346
    | exact resolve eq17346 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17346 eq17359
  have eq17923 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq747 x x
       have i₂ := eq17806
       grind)
    | exact superpose eq17806 eq747
    | (have j0 := eq747 x x
       grind)
    | exact resolve eq747 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq17806
  have eq17926 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17923
  have eq17927 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17926
  have eq17936 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17927
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17927
    | exact resolve eq17927 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17927
  have eq17955 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17566 eq17936
    | exact resolve eq17936 eq17566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17566 eq17936
  have eq18156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17955 eq17673
    | exact resolve eq17673 eq17955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17673 eq17955
  have eq18157 : False := by grind
  exact eq18157

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyy_x_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X0) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
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
  have eq67 : y ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq118 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq107
  have eq119 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq104
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq123
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq123
    | exact resolve eq123 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq163 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq183 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq41
    | exact resolve eq41 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq209 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq212 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) X0) x) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) X0) (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq54 X0 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq285 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq308 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq399 : (k y (k y y)) = (τ (k (σ y) (k (σ y) (σ y)))) := by
    first
    | exact superpose eq89 eq285
    | exact resolve eq285 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq448 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq308 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq308
    | (have j0 := eq308 X0 y
       grind)
    | exact resolve eq308 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq485 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op (M.op X0 (M.op X1 X2)) X0) X2
       have i₂ := eq14 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : (k (k x y) y) = (τ (k (k (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq61 eq448
    | exact resolve eq448 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq551 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X0 X1) X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x)))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x y) x)) X0)) (M.op x X2)) := by
    intro X0 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq570 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0)) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq585 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 (M.op (M.op X0 X0) X0) x
       have i₂ := eq54 (M.op X0 (M.op (M.op X0 X0) X0)) x
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq718 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq215 sF4
       have i₂ := eq54 sF4 sF2
       grind)
    | exact superpose eq54 eq215
    | exact resolve eq215 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x)
       have i₂ := eq225 X0 x x
       grind)
    | exact superpose eq225 eq54
    | exact resolve eq54 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1026 X0
       have i₂ := eq225 X0 X0 X0
       grind)
    | exact superpose eq225 eq1026
    | exact resolve eq1026 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq3809 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (σ x)) := by
    first
    | (have i₁ := eq581 (M.op (M.op sF4 sF4) sF4)
       have i₂ := eq1030 sF4
       grind)
    | exact superpose eq1030 eq581
    | exact resolve eq581 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3834 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3809
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq3809
    | exact resolve eq3809 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3854 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3834 eq581
    | exact resolve eq581 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq4029 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq718 eq245
    | exact resolve eq245 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq718
  have eq4062 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq4029 X0
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq4029
    | exact resolve eq4029 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4029
  have eq4063 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4062 x
       have i₂ := eq54 sF4 x
       grind)
    | exact superpose eq54 eq4062
    | exact resolve eq4062 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062
  have eq4064 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3834 eq4063
    | exact resolve eq4063 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834 eq4063
  have eq4065 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4064 eq3854
    | exact resolve eq3854 eq4064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064
  have eq5240 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 (M.op (M.op X0 X0) X0) (M.op X0 X1) x
       have i₂ := eq225 X0 X1 x
       grind)
    | exact superpose eq225 eq485
    | exact resolve eq485 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq5332 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5240 X0 X1
       have i₂ := eq14 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq14 eq5240
    | exact resolve eq5240 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq5342 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5332 X0 x
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq5332
    | exact resolve eq5332 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5332
  have eq6423 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq163
    | (have j0 := eq163 x
       grind)
    | exact resolve eq163 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq6442 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6423
  have eq6446 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6442
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6442
    | exact resolve eq6442 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6442
  have eq6463 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6446
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6446 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446
  have eq6665 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq191
    | (have j0 := eq191 y
       grind)
    | exact resolve eq191 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq6681 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6665
  have eq6684 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6681
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq6681
    | exact resolve eq6681 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681
  have eq6708 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6684
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6684 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684
  have eq6735 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6708 eq89
    | exact resolve eq89 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq6737 : (k y (k y y)) = (τ (k (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq6708 eq399
    | exact resolve eq399 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq6902 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq209
    | (have j0 := eq209 (M.op x y)
       grind)
    | exact resolve eq209 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq6917 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6902
  have eq6919 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq6917
    | exact resolve eq6917 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq6917
  have eq6950 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6919
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6919 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919
  have eq7084 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq551 X0 X1 X2 X3
       have i₂ := eq5342 X0
       grind)
    | exact superpose eq5342 eq551
    | exact resolve eq551 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq7108 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7084 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x) X3 X4
       have i₂ := eq225 X0 x x
       grind)
    | exact superpose eq225 eq7084
    | exact resolve eq7084 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7084
  have eq7293 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7108 x X3 X4
       have i₂ := eq218 x x
       grind)
    | exact superpose eq218 eq7108
    | exact resolve eq7108 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7108
  have eq7333 : ∀ X0 X3 X4 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7293 X0 X3 X4
       have i₂ := eq1030 X0
       grind)
    | exact superpose eq1030 eq7293
    | exact resolve eq7293 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293
  have eq7348 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7333 X0 X3 X4
       have i₂ := eq5342 X0
       grind)
    | exact superpose eq5342 eq7333
    | exact resolve eq7333 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7333
  have eq7415 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq7348
    | (have j0 := eq7348 (σ x) (σ y) X0
       grind)
    | exact resolve eq7348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7680 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 X0) (M.op x X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq569 x X2
       have i₂ := eq7348 x (M.op sF0 x) x
       grind)
    | exact superpose eq7348 eq569
    | exact resolve eq569 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq7701 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op x X1)) x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7680 eq212
    | exact resolve eq212 eq7680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq7680
  have eq7847 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq7701 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7701
    | (have j0 := eq7701 X0 y
       grind)
    | exact resolve eq7701 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7701
  have eq7893 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq7847 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0 X0 X0
       grind)
    | exact superpose eq225 eq7847
    | exact resolve eq7847 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7973 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 X0) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq570 x X2
       have i₂ := eq7348 x (M.op sF4 sF2) x
       grind)
    | exact superpose eq7348 eq570
    | exact resolve eq570 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq7348
  have eq7995 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) X1)) (σ x)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7973 eq215
    | exact resolve eq215 eq7973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq7973
  have eq8143 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq7995
    | (have j0 := eq7995 X0 (σ y)
       grind)
    | exact resolve eq7995 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995
  have eq8189 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8143 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0 X0 X0
       grind)
    | exact superpose eq225 eq8143
    | exact resolve eq8143 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8143
  have eq8269 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq585 X0
       have i₂ := eq5342 X0
       grind)
    | exact superpose eq5342 eq585
    | exact resolve eq585 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq8533 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq223 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8269 X0
       grind)
    | exact superpose eq8269 eq223
    | (have j0 := eq223 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq223 (M.op X0 X0) X0
       have r₂ := eq8269 X0
       grind)
    | exact resolve eq223 eq8269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq8269
  have eq8540 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq8533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8533
  have eq8544 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq8540 X0
       have i₂ := eq218 X0 X0
       grind)
    | exact superpose eq218 eq8540
    | exact resolve eq8540 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq8540
  have eq8562 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8544 X0
       have i₂ := eq1030 X0
       grind)
    | exact superpose eq1030 eq8544
    | exact resolve eq8544 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8544
  have eq8576 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq8562 (M.op (M.op x x) x)
       have i₂ := eq225 x x x
       grind)
    | exact superpose eq225 eq8562
    | exact resolve eq8562 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq8562
  have eq8605 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8576 X0
       have i₂ := eq5342 X0
       grind)
    | exact superpose eq5342 eq8576
    | exact resolve eq8576 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5342 eq8576
  have eq9043 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) := by
    first
    | exact superpose eq3854 eq7893
    | exact resolve eq7893 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq9047 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1030 X0
       have i₂ := eq7893 X0
       grind)
    | exact superpose eq7893 eq1030
    | exact resolve eq1030 eq7893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9929 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq8189 eq14
    | exact resolve eq14 eq8189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8189
  have eq9956 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9929 X1 X1
       have i₂ := eq14 X1 X1 sF4
       grind)
    | exact superpose eq14 eq9929
    | exact resolve eq9929 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9929
  have eq12933 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9956 eq556
    | exact resolve eq556 eq9956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq9956
  have eq12934 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4065 eq12933
    | exact resolve eq12933 eq4065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065 eq12933
  have eq12935 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9043 eq12934
    | exact resolve eq12934 eq9043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9043 eq12934
  have eq12936 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7415 eq12935
    | exact resolve eq12935 eq7415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7415 eq12935
  have eq12975 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (σ y)) := by
    first
    | (have i₁ := eq12936 (M.op (M.op x x) x) sF3 x
       have i₂ := eq57 x sF3 x
       grind)
    | exact superpose eq57 eq12936
    | exact resolve eq12936 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq12936
  have eq32080 : (k y (k y y)) = (τ (M.op (M.op (σ y) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq6737
       have i₂ := eq8605 sF3
       grind)
    | exact superpose eq8605 eq6737
    | exact resolve eq6737 eq8605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6737
  have eq32081 : (k y (k y y)) = (τ (M.op (M.op (σ y) (M.op x y)) x)) := by
    first
    | (have i₁ := eq32080
       have i₂ := eq7893 sF3
       grind)
    | exact superpose eq7893 eq32080
    | exact resolve eq32080 eq7893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893 eq32080
  have eq41180 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6708 eq118
    | exact resolve eq118 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq41181 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6463 eq119
    | exact resolve eq119 eq6463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq6463
  have eq41192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq124 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq41202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq41192
    | exact resolve eq41192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41192
  have eq41213 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq41202
       have r₂ := eq28
       grind)
    | exact resolve eq41202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41202
  have eq41215 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq41213
    | exact resolve eq41213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41213
  have eq41221 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq41215 eq6735
    | exact resolve eq6735 eq41215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41215
  have eq41349 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq41221
    | exact resolve eq41221 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41221
  have eq43866 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq41349
       grind)
    | exact superpose eq41349 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq41349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43884 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43866
  have eq50190 : y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq43884
       grind)
    | exact superpose eq43884 eq79
    | exact resolve eq79 eq43884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50260 : x ≠ y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43884
  have eq50930 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41349
       have i₂ := eq50190
       grind)
    | exact superpose eq50190 eq41349
    | exact resolve eq41349 eq50190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41349 eq50190
  have eq50960 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq50930
  have eq50975 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq50960
       have r₂ := eq50260
       grind)
    | exact resolve eq50960 eq50260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50260 eq50960
  have eq51029 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8605 y
       have i₂ := eq50975
       grind)
    | exact superpose eq50975 eq8605
    | exact resolve eq8605 eq50975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51043 : x ≠ y ∨ x = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq50975
       grind)
    | exact superpose eq50975 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq50975
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq50975
       grind)
    | exact resolve eq13 eq50975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51118 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51029
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51029
    | exact resolve eq51029 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51029
  have eq51581 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq51118
       grind)
    | exact superpose eq51118 eq76
    | exact resolve eq76 eq51118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51118
  have eq51620 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq51581
    | exact resolve eq51581 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51581
  have eq75399 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41180
       have i₂ := eq50975
       grind)
    | exact superpose eq50975 eq41180
    | exact resolve eq41180 eq50975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41180 eq50975
  have eq75479 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75399
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq75399
    | exact resolve eq75399 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75399
  have eq75496 : (τ (σ x)) = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75479 eq6735
    | exact resolve eq6735 eq75479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75479
  have eq75679 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq75496
    | exact resolve eq75496 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75496
  have eq75698 : x = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq75679
       have r₂ := eq51043
       grind)
    | exact resolve eq75679 eq51043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51043 eq75679
  have eq75709 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq75698
       grind)
    | exact superpose eq75698 eq77
    | exact resolve eq77 eq75698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq75714 : (σ (k x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq75698
       grind)
    | exact superpose eq75698 eq183
    | exact resolve eq183 eq75698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq75698
  have eq75774 : (σ (k x y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6708 eq75714
    | exact resolve eq75714 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75714
  have eq75779 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6708 eq75709
    | exact resolve eq75709 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6708 eq75709
  have eq75792 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75774
       have i₂ := eq79 sF3
       grind)
    | exact superpose eq79 eq75774
    | exact resolve eq75774 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75774
  have eq75797 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75779
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq75779
    | exact resolve eq75779 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75779
  have eq75808 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75792
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq75792
    | exact resolve eq75792 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75792
  have eq75818 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq75808
       have r₂ := eq68
       grind)
    | exact resolve eq75808 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq75808
  have eq75831 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75818 eq61
    | exact resolve eq61 eq75818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq75837 : (k (k x y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75818 eq519
    | exact resolve eq519 eq75818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq75818
  have eq75894 : (τ (M.op (σ y) (σ y))) = (k (k x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75837
       have i₂ := eq79 sF3
       grind)
    | exact superpose eq79 eq75837
    | exact resolve eq75837 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75837
  have eq75899 : (k x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6735 eq75831
    | exact resolve eq75831 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75831
  have eq75906 : (k y y) = (k (k x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6735 eq75894
    | exact resolve eq75894 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6735 eq75894
  have eq76048 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq75899
       grind)
    | exact superpose eq75899 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq75899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75899
  have eq76066 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq76048
  have eq76089 : (k x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq76066
       have r₂ := eq67
       grind)
    | exact resolve eq76066 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq76066
  have eq76177 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75797 eq8605
    | exact resolve eq8605 eq75797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75797
  have eq76296 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq76177
    | exact resolve eq76177 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76177
  have eq77148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76296 eq51620
    | exact resolve eq51620 eq76296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51620 eq76296
  have eq77163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq77148
  have eq77171 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq77163
       have r₂ := eq28
       grind)
    | exact resolve eq77163 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77163
  have eq77240 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (M.op x y)) x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77171 eq12975
    | exact resolve eq12975 eq77171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975 eq77171
  have eq77314 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9047 eq77240
    | exact resolve eq77240 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9047 eq77240
  have eq77477 : (σ x) = (M.op (M.op (σ y) (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77314 eq7847
    | exact resolve eq7847 eq77314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847 eq77314
  have eq81402 : (τ (σ x)) = (k y (k y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77477 eq32081
    | exact resolve eq32081 eq77477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32081 eq77477
  have eq81502 : x = (k y (k y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq81402
    | exact resolve eq81402 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq81402
  have eq91114 : (k y y) = (k (M.op y y) y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75906
       have i₂ := eq76089
       grind)
    | exact superpose eq76089 eq75906
    | exact resolve eq75906 eq76089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75906 eq76089
  have eq91145 : (M.op y y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91114
       have i₂ := eq79 y
       grind)
    | exact superpose eq79 eq91114
    | exact resolve eq91114 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91114
  have eq91160 : (M.op y y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq91145
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq91145
       have r₂ := eq13 y y
       grind)
    | exact resolve eq91145 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91145
  have eq91226 : x = (k y (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq81502
       have i₂ := eq91160
       grind)
    | exact superpose eq91160 eq81502
    | exact resolve eq81502 eq91160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81502 eq91160
  have eq91254 : x = (k y (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq91226
  have eq91283 : x = (M.op (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91254
       have i₂ := eq8605 y
       grind)
    | exact superpose eq8605 eq91254
    | exact resolve eq91254 eq8605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8605 eq91254
  have eq91563 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1030 y
       have i₂ := eq91283
       grind)
    | exact superpose eq91283 eq1030
    | exact resolve eq1030 eq91283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq91283
  have eq91713 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91563
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91563
    | exact resolve eq91563 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91563
  have eq91714 : y = (M.op x y) := by grind
  clear eq91713
  have eq91743 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq91714 eq21
    | exact resolve eq21 eq91714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq91794 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq91714 eq221
    | exact resolve eq221 eq91714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq91930 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq91794
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91794
    | exact resolve eq91794 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq91794
  have eq91975 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq91743
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq91743
    | exact resolve eq91743 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91743
  have eq91983 : y = (M.op x x) := by
    first
    | exact superpose eq91714 eq91930
    | exact resolve eq91930 eq91714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91714 eq91930
  have eq92056 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq91975 eq27
    | exact resolve eq27 eq91975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq92377 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq41181
       have i₂ := eq91983
       grind)
    | exact superpose eq91983 eq41181
    | exact resolve eq41181 eq91983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41181
  have eq92407 : y = (k y x) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq91983
       grind)
    | exact superpose eq91983 eq79
    | exact resolve eq79 eq91983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq91983
  have eq92537 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92377
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq92377
    | exact resolve eq92377 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92377
  have eq92562 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq91975 eq92537
    | exact resolve eq92537 eq91975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92537
  have eq92661 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq92407
       grind)
    | exact superpose eq92407 eq76
    | exact resolve eq76 eq92407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq92407
  have eq92711 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq91975 eq92661
    | exact resolve eq92661 eq91975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92661
  have eq92728 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq92711
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq92711
    | exact resolve eq92711 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92711
  have eq92745 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq91975 eq92728
    | exact resolve eq92728 eq91975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92728
  have eq95537 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq92562 eq54
    | exact resolve eq54 eq92562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq92562
  have eq95586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq92056 eq95537
    | exact resolve eq95537 eq92056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95537
  have eq95619 : x = y := by
    first
    | (have r₁ := eq95586
       have r₂ := eq28
       grind)
    | exact resolve eq95586 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95586
  have eq95646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq95619
       grind)
    | exact superpose eq95619 eq25
    | exact resolve eq25 eq95619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq95667 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq95619
       grind)
    | exact superpose eq95619 eq133
    | exact resolve eq133 eq95619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq95619
  have eq96009 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq91975 eq95667
    | exact resolve eq95667 eq91975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95667
  have eq96030 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq91975 eq95646
    | exact resolve eq95646 eq91975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91975 eq95646
  have eq96158 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq6950 eq96009
    | exact resolve eq96009 eq6950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6950 eq96009
  have eq96179 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96030
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96030
    | exact resolve eq96030 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq96030
  have eq96265 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq132 eq96158
    | exact resolve eq96158 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq96158
  have eq96337 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq92745 eq96265
    | exact resolve eq96265 eq92745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92745 eq96265
  have eq96746 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq96179 eq92056
    | exact resolve eq92056 eq96179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92056 eq96179
  have eq98105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96337 eq96746
    | exact resolve eq96746 eq96337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96337 eq96746
  have eq98106 : False := by grind
  exact eq98106

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_pyy_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
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
  have eq47 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X0) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op X0 x) X0) (M.op x y)) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq69
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq74
    | exact resolve eq74 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
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
  clear eq37
  have eq103 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq157 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq119
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq165 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq157
  have eq211 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) X0) x) = X0 := by
    intro X0
    first
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) X0) (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq50 X0 X0
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op X0 x) X0) = (M.op (M.op X0 (M.op (M.op X0 x) X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq445 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op (M.op X0 (M.op X1 X2)) X0) X2
       have i₂ := eq14 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X1 X3
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 X0 (M.op X0 X1) X2 X3
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) x)) = (M.op (M.op (M.op (M.op x y) x) (M.op x (M.op (M.op x y) x))) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x)))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x y) x)) X0)) (M.op x X2)) := by
    intro X0 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0)) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X0)) x) := by
    intro X0
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq785 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0 (M.op (M.op X0 X0) X0) x
       have i₂ := eq50 (M.op X0 (M.op (M.op X0 X0) X0)) x
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq798 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) x) := by
    first
    | (have i₁ := eq211 sF0
       have i₂ := eq50 sF0 x
       grind)
    | exact superpose eq50 eq211
    | exact resolve eq211 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq214 sF4
       have i₂ := eq50 sF4 sF2
       grind)
    | exact superpose eq50 eq214
    | exact resolve eq214 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq879 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq882 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq1205 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x)
       have i₂ := eq224 X0 x x
       grind)
    | exact superpose eq224 eq50
    | exact resolve eq50 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1205 X0
       have i₂ := eq224 X0 X0 X0
       grind)
    | exact superpose eq224 eq1205
    | exact resolve eq1205 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq3718 : (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) x) := by
    first
    | (have i₁ := eq780 (M.op (M.op sF0 sF0) sF0)
       have i₂ := eq1209 sF0
       grind)
    | exact superpose eq1209 eq780
    | exact resolve eq780 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3743 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq3718
       have i₂ := eq14 sF0 sF0 (M.op (M.op sF0 sF0) sF0)
       grind)
    | exact superpose eq14 eq3718
    | exact resolve eq3718 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3718
  have eq3746 : (M.op (M.op (M.op x y) x) x) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq3743 eq780
    | exact resolve eq780 eq3743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq3791 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (σ x)) := by
    first
    | (have i₁ := eq781 (M.op (M.op sF4 sF4) sF4)
       have i₂ := eq1209 sF4
       grind)
    | exact superpose eq1209 eq781
    | exact resolve eq781 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3816 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3791
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq3791
    | exact resolve eq3791 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3834 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3816 eq781
    | exact resolve eq781 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq3918 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq798 eq239
    | exact resolve eq239 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq798
  have eq3949 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3918 X0
       have i₂ := eq14 sF0 sF0 (M.op (M.op sF0 sF0) sF0)
       grind)
    | exact superpose eq14 eq3918
    | exact resolve eq3918 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918
  have eq3950 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq3949 x
       have i₂ := eq50 sF0 x
       grind)
    | exact superpose eq50 eq3949
    | exact resolve eq3949 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3949
  have eq3951 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3743 eq3950
    | exact resolve eq3950 eq3743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743 eq3950
  have eq3952 : (M.op (M.op (M.op x y) x) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq3951 eq3746
    | exact resolve eq3746 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746
  have eq3993 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq821 eq244
    | exact resolve eq244 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq821
  have eq4024 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq3993 X0
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq3993
    | exact resolve eq3993 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993
  have eq4025 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4024 x
       have i₂ := eq50 sF4 x
       grind)
    | exact superpose eq50 eq4024
    | exact resolve eq4024 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4026 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3816 eq4025
    | exact resolve eq4025 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq4025
  have eq4027 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4026 eq3834
    | exact resolve eq3834 eq4026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq5181 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 (M.op (M.op X0 X0) X0) (M.op X0 X1) x
       have i₂ := eq224 X0 X1 x
       grind)
    | exact superpose eq224 eq445
    | exact resolve eq445 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq5273 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5181 X0 X1
       have i₂ := eq14 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq14 eq5181
    | exact resolve eq5181 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq5284 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5273 X0 x
       have i₂ := eq50 X0 x
       grind)
    | exact superpose eq50 eq5273
    | exact resolve eq5273 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq6666 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq751 X0 X1 X2 X3
       have i₂ := eq5284 X0
       grind)
    | exact superpose eq5284 eq751
    | exact resolve eq751 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq6785 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6666 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x) X3 X4
       have i₂ := eq224 X0 x x
       grind)
    | exact superpose eq224 eq6666
    | exact resolve eq6666 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666
  have eq6969 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6785 x X3 X4
       have i₂ := eq217 x x
       grind)
    | exact superpose eq217 eq6785
    | exact resolve eq6785 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq6785
  have eq7009 : ∀ X0 X3 X4 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6969 X0 X3 X4
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq6969
    | exact resolve eq6969 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6969
  have eq7024 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7009 X0 X3 X4
       have i₂ := eq5284 X0
       grind)
    | exact superpose eq5284 eq7009
    | exact resolve eq7009 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009
  have eq7084 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq7024 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7024
    | (have j0 := eq7024 x y X0
       grind)
    | exact resolve eq7024 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7091 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq7024
    | (have j0 := eq7024 (σ x) (σ y) X0
       grind)
    | exact resolve eq7024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7348 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 X0) (M.op x X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq769 x X2
       have i₂ := eq7024 x (M.op sF0 x) x
       grind)
    | exact superpose eq7024 eq769
    | exact resolve eq769 eq7024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq7369 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op x X1)) x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7348 eq211
    | exact resolve eq211 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq7348
  have eq7506 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq7369 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7369
    | (have j0 := eq7369 X0 y
       grind)
    | exact resolve eq7369 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7552 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq7506 (M.op (M.op X0 X0) X0)
       have i₂ := eq224 X0 X0 X0
       grind)
    | exact superpose eq224 eq7506
    | exact resolve eq7506 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7506
  have eq7633 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 X0) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq770 x X2
       have i₂ := eq7024 x (M.op sF4 sF2) x
       grind)
    | exact superpose eq7024 eq770
    | exact resolve eq770 eq7024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq7655 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) X1)) (σ x)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7633 eq214
    | exact resolve eq214 eq7633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq7633
  have eq7794 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq7655
    | (have j0 := eq7655 X0 (σ y)
       grind)
    | exact resolve eq7655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7655
  have eq7840 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7794 (M.op (M.op X0 X0) X0)
       have i₂ := eq224 X0 X0 X0
       grind)
    | exact superpose eq224 eq7794
    | exact resolve eq7794 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq7794
  have eq7921 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq785 X0
       have i₂ := eq5284 X0
       grind)
    | exact superpose eq5284 eq785
    | exact resolve eq785 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq5284
  have eq8376 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) := by
    first
    | exact superpose eq3834 eq7552
    | exact resolve eq7552 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq8379 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1209 X0
       have i₂ := eq7552 X0
       grind)
    | exact superpose eq7552 eq1209
    | exact resolve eq1209 eq7552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8459 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op x y))) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq7552 eq14
    | exact resolve eq14 eq7552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7552
  have eq8484 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8459 X1 X1
       have i₂ := eq14 X1 X1 sF0
       grind)
    | exact superpose eq14 eq8459
    | exact resolve eq8459 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8459
  have eq9078 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1209 X0
       have i₂ := eq7840 X0
       grind)
    | exact superpose eq7840 eq1209
    | exact resolve eq1209 eq7840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq9147 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7840 eq14
    | exact resolve eq14 eq7840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7840
  have eq9172 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9147 X1 X1
       have i₂ := eq14 X1 X1 sF4
       grind)
    | exact superpose eq14 eq9147
    | exact resolve eq9147 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9147
  have eq11671 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) x)) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq755 X0 X1 X2
       have i₂ := eq8484 (M.op sF0 x) (M.op sF0 x)
       grind)
    | exact superpose eq8484 eq755
    | exact resolve eq755 eq8484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq11672 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) x)) = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3952 eq11671
    | exact resolve eq11671 eq3952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952 eq11671
  have eq11673 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7084 eq11672
    | exact resolve eq11672 eq7084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7084 eq11672
  have eq11780 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | (have i₁ := eq11673 (M.op (M.op x x) x) y x
       have i₂ := eq53 x y x
       grind)
    | exact superpose eq53 eq11673
    | exact resolve eq11673 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11673
  have eq11904 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9172 eq756
    | exact resolve eq756 eq9172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq11905 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4027 eq11904
    | exact resolve eq11904 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027 eq11904
  have eq11906 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq8376 eq11905
    | exact resolve eq11905 eq8376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8376 eq11905
  have eq11907 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7091 eq11906
    | exact resolve eq11906 eq7091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7091 eq11906
  have eq11946 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (σ y)) := by
    first
    | (have i₁ := eq11907 (M.op (M.op x x) x) sF3 x
       have i₂ := eq53 x sF3 x
       grind)
    | exact superpose eq53 eq11907
    | exact resolve eq11907 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11907
  have eq13505 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = (M.op (M.op X0 X0) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq451 X0 X1 X2 X3
       have i₂ := eq7024 X0 (M.op (M.op X1 X2) X1) X0
       grind)
    | exact superpose eq7024 eq451
    | exact resolve eq451 eq7024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq13890 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 x
       have i₂ := eq13505 X0 X1 x X2
       grind)
    | exact superpose eq13505 eq53
    | exact resolve eq53 eq13505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq13505
  have eq14359 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq3951 eq13890
    | exact resolve eq13890 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14541 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq7369 (M.op (M.op x X0) (M.op x X0)) X0
       have i₂ := eq13890 (M.op x X0) (M.op x X0) (M.op x X0)
       grind)
    | exact superpose eq13890 eq7369
    | exact resolve eq7369 eq13890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7369 eq13890
  have eq14626 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14541 X0
       have i₂ := eq8484 (M.op x X0) X0
       grind)
    | (have i₁ := eq14541 y
       have i₂ := eq8484 (M.op x y) x
       grind)
    | exact superpose eq8484 eq14541
    | exact resolve eq14541 eq8484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8484 eq14541
  have eq18165 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq222 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq18184 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18165 X0
       have i₂ := eq7921 X0
       grind)
    | exact superpose eq7921 eq18165
    | (have j0 := eq18165 X0
       grind)
    | exact resolve eq18165 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18165
  have eq18237 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18184 X0
       have i₂ := eq7921 X0
       grind)
    | exact superpose eq7921 eq18184
    | (have j0 := eq18184 X0
       grind)
    | exact resolve eq18184 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18184
  have eq24213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq24220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24213
    | exact resolve eq24213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24213
  have eq24231 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24220
       have r₂ := eq28
       grind)
    | exact resolve eq24220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24220
  have eq24233 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq24231
    | exact resolve eq24231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24231
  have eq24239 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq24233
  have eq24344 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24239 eq61
    | exact resolve eq61 eq24239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq24239
  have eq24371 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq24344
    | exact resolve eq24344 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24344
  have eq32401 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq24371
       grind)
    | exact superpose eq24371 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq24371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24371
  have eq32411 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq32401
  have eq32420 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32411
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32411
    | exact resolve eq32411 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32411
  have eq32421 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32420
  have eq32472 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq32520 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14359 y y
       have i₂ := eq32421
       grind)
    | exact superpose eq32421 eq14359
    | exact resolve eq14359 eq32421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32421
  have eq32541 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11780 eq32520
    | exact resolve eq32520 eq11780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32520
  have eq33598 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq879 x y
       have i₂ := eq32472
       grind)
    | exact superpose eq32472 eq879
    | (have j0 := eq879 x y
       grind)
    | exact resolve eq879 eq32472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq32472
  have eq33602 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33598
  have eq33607 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33602
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33602
    | exact resolve eq33602 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33602
  have eq33622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33607
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33607
    | exact resolve eq33607 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33607
  have eq33630 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq33622
    | exact resolve eq33622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33622
  have eq33631 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq33630
  have eq33638 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33631
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33631
    | exact resolve eq33631 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33631
  have eq33646 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33638
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33638
    | exact resolve eq33638 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33638
  have eq33769 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32541
  have eq35730 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33646 eq7921
    | exact resolve eq7921 eq33646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq35762 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33646 eq7024
    | exact resolve eq7024 eq33646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024 eq33646
  have eq35793 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9172 eq35762
    | (have j0 := eq35762 (σ y)
       grind)
    | exact resolve eq35762 eq9172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9172 eq35762
  have eq35808 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq35730
    | exact resolve eq35730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35730
  have eq36842 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33769 eq896
    | (have j0 := eq896 x x
       grind)
    | exact resolve eq896 eq33769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33769
  have eq36844 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36842
  have eq36849 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36844
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36844
    | exact resolve eq36844 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36844
  have eq36864 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36849
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36849
    | exact resolve eq36849 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36849
  have eq36872 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq36864
    | exact resolve eq36864 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36864
  have eq38256 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35793 eq9078
    | exact resolve eq9078 eq35793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9078 eq35793
  have eq43342 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3951 eq165
    | exact resolve eq165 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq43343 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3951 eq43342
    | exact resolve eq43342 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951 eq43342
  have eq177178 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36872 eq38256
    | exact resolve eq38256 eq36872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36872 eq38256
  have eq177374 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq177178
  have eq177468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq177374
    | exact resolve eq177374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177374
  have eq177469 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq177468
  have eq178284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq177469 eq35808
    | exact resolve eq35808 eq177469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35808 eq177469
  have eq178489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq178284
  have eq178545 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq178489
       have r₂ := eq28
       grind)
    | exact resolve eq178489 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178489
  have eq178573 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq178545 eq28
    | exact resolve eq28 eq178545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178639 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (M.op x y)) x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq178545 eq11946
    | exact resolve eq11946 eq178545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11946 eq178545
  have eq178677 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8379 eq178639
    | exact resolve eq178639 eq8379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8379 eq178639
  have eq179061 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq178677
  have eq179960 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq179061 eq103
    | exact resolve eq103 eq179061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq180011 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq179960
    | exact resolve eq179960 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq179960
  have eq180341 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq180011
       grind)
    | exact superpose eq180011 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq180011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180353 : y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq180341
  have eq253202 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x x
       have i₂ := eq180353
       grind)
    | exact superpose eq180353 eq50
    | exact resolve eq50 eq180353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180353
  have eq253321 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq253202
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq253202
    | exact resolve eq253202 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253202
  have eq253322 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq253321
  have eq254017 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq253322
       grind)
    | exact superpose eq253322 eq51
    | exact resolve eq51 eq253322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq254047 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14359 y x
       have i₂ := eq253322
       grind)
    | exact superpose eq253322 eq14359
    | exact resolve eq14359 eq253322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14359 eq253322
  have eq254149 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11780 eq254047
    | exact resolve eq254047 eq11780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780 eq254047
  have eq254166 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14626 eq254017
    | exact resolve eq254017 eq14626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14626 eq254017
  have eq254192 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq254166
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq254166
    | exact resolve eq254166 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254166
  have eq254256 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq254149
  have eq255094 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq254192 eq47
    | exact resolve eq47 eq254192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq255144 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq254192 eq43343
    | exact resolve eq43343 eq254192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43343 eq254192
  have eq255277 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq255144
  have eq255326 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq255277
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq255277
    | exact resolve eq255277 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255277
  have eq255337 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq255094 x
       have i₂ := eq50 y x
       grind)
    | exact superpose eq50 eq255094
    | exact resolve eq255094 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255094
  have eq255362 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq254256 eq117
    | exact resolve eq117 eq254256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq254256
  have eq255414 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq255362
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq255362
    | exact resolve eq255362 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255362
  have eq256231 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18237 y
       have i₂ := eq255337
       grind)
    | exact superpose eq255337 eq18237
    | exact resolve eq18237 eq255337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18237 eq255337
  have eq256422 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq256231
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq256231
    | exact resolve eq256231 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256231
  have eq256482 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq256422
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq256422
    | exact resolve eq256422 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256422
  have eq256483 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq256482
  have eq257808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq256483
       grind)
    | exact superpose eq256483 eq93
    | exact resolve eq93 eq256483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq257828 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180011
       have i₂ := eq256483
       grind)
    | exact superpose eq256483 eq180011
    | exact resolve eq180011 eq256483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180011 eq256483
  have eq257840 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq257828
  have eq257872 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq257808
    | exact resolve eq257808 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257808
  have eq257980 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq257840 eq220
    | exact resolve eq220 eq257840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257840
  have eq258274 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq257980
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq257980
    | exact resolve eq257980 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257980
  have eq260062 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq257872 eq179061
    | exact resolve eq179061 eq257872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179061 eq257872
  have eq260087 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq260062
  have eq260530 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq260087 eq255414
    | exact resolve eq255414 eq260087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255414 eq260087
  have eq260535 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq260530
  have eq261417 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq258274
       grind)
    | exact superpose eq258274 eq73
    | exact resolve eq73 eq258274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq258274
  have eq261611 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq261417
  have eq261682 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq261611
    | exact resolve eq261611 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261611
  have eq262050 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq260535 eq255326
    | exact resolve eq255326 eq260535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255326 eq260535
  have eq262083 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq262050
  have eq262102 : y = (M.op x y) := by
    first
    | (have r₁ := eq262083
       have r₂ := eq178573
       grind)
    | exact resolve eq262083 eq178573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178573 eq262083
  have eq262120 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq262102 eq21
    | exact resolve eq21 eq262102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq262173 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq262102 eq220
    | exact resolve eq220 eq262102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq262470 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq262173
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq262173
    | exact resolve eq262173 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq262173
  have eq262516 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq262120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq262120
    | exact resolve eq262120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262120
  have eq262525 : y = (M.op x x) := by
    first
    | exact superpose eq262102 eq262470
    | exact resolve eq262470 eq262102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262470
  have eq262528 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq262516 eq27
    | exact resolve eq27 eq262516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq264190 : x = (k y x) := by grind
  clear eq262525
  have eq264656 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq896 y x
       have i₂ := eq264190
       grind)
    | exact superpose eq264190 eq896
    | (have j0 := eq896 x x
       grind)
    | exact resolve eq896 eq264190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq264190
  have eq264659 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq264656
  have eq264665 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq264659
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq264659
    | exact resolve eq264659 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264659
  have eq264688 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq264665
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq264665
    | exact resolve eq264665 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264665
  have eq264711 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq264688
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq264688
    | exact resolve eq264688 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264688
  have eq264723 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq262516 eq264711
    | exact resolve eq264711 eq262516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264711
  have eq276792 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq262102 eq261682
    | exact resolve eq261682 eq262102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261682 eq262102
  have eq315416 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  have eq315582 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq264723
  have eq321291 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq315416 eq276792
    | exact resolve eq276792 eq315416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276792 eq315416
  have eq321335 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq321291
       have r₂ := eq315582
       grind)
    | exact resolve eq321291 eq315582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321291
  have eq321542 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq321335 eq50
    | exact resolve eq50 eq321335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq321335
  have eq321639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq262528 eq321542
    | exact resolve eq321542 eq262528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321542
  have eq321706 : x = y := by
    first
    | (have r₁ := eq321639
       have r₂ := eq28
       grind)
    | exact resolve eq321639 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321639
  have eq321751 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq321706
       grind)
    | exact superpose eq321706 eq25
    | exact resolve eq25 eq321706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq321706
  have eq322444 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq262516 eq321751
    | exact resolve eq321751 eq262516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262516 eq321751
  have eq322724 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq322444
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq322444
    | exact resolve eq322444 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq322444
  have eq323479 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq322724 eq262528
    | exact resolve eq262528 eq322724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262528
  have eq323492 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq322724 eq315582
    | (have r₁ := eq315582
       have r₂ := eq322724
       grind)
    | exact resolve eq315582 eq322724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315582 eq322724
  have eq323494 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq323492
  have eq328437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq323479 eq323494
    | exact resolve eq323494 eq323479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323479 eq323494
  have eq328438 : False := by grind
  exact eq328438

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq62 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq63 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq82 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 (σ X0) (σ X1)
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq82 y x
       grind)
    | exact superpose eq82 eq74
    | (have j1 := eq82 y x
       grind)
    | exact resolve eq74 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq113
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq82
    | (have j0 := eq82 (σ y) (σ x)
       grind)
    | exact resolve eq82 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq141 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq63
    | exact resolve eq63 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq142 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq67
    | (have r₁ := eq67
       have r₂ := eq127
       grind)
    | exact resolve eq67 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq127
  have eq423 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq422
  have eq424 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq423
       have r₂ := eq141
       grind)
    | exact resolve eq423 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq423
  have eq427 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq424 eq114
    | exact resolve eq114 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq424
  have eq431 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq427
  have eq436 : x = (M.op x y) := by
    first
    | (have r₁ := eq431
       have r₂ := eq142
       grind)
    | exact resolve eq431 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq431
  have eq439 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq436 eq20
    | exact resolve eq20 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq436 eq62
    | exact resolve eq62 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq442 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq436 eq66
    | (have r₁ := eq66
       have r₂ := eq436
       grind)
    | exact resolve eq66 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq448 : x = y ∨ x = (k y x) := by grind
  clear eq442
  have eq455 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq439
    | exact resolve eq439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq462 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq455 eq26
    | exact resolve eq26 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq502 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq94
    | (have j0 := eq94 X0 (M.op x y)
       grind)
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq94
  have eq549 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq436 eq502
    | (have j0 := eq502 X0
       grind)
    | exact resolve eq502 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq603 : x = (k y x) := by
    first
    | (have r₁ := eq448
       have r₂ := eq441
       grind)
    | exact resolve eq448 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq448
  have eq634 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq549 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq549
    | (have j0 := eq549 y
       grind)
    | exact resolve eq549 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq549
  have eq642 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq462 eq634
    | exact resolve eq634 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq657 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq642
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq642
    | exact resolve eq642 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq642
  have eq668 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq455 eq657
    | exact resolve eq657 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq462 eq668
    | exact resolve eq668 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq668
  have eq683 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq677
       have r₂ := eq27
       grind)
    | exact resolve eq677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq689 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq683 eq92
    | exact resolve eq92 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq683
  have eq691 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq436 eq689
    | exact resolve eq689 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq689
  have eq692 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq691
       have i₂ := eq603
       grind)
    | exact superpose eq603 eq691
    | exact resolve eq691 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq691
  have eq694 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq692 eq15
    | exact resolve eq15 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq705 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq694
    | exact resolve eq694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq694
  have eq709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq455 eq705
    | exact resolve eq705 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq705
  have eq712 : False := by grind
  exact eq712

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(X,X) = m(Y,Y) then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_y_pyx_y_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq20 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq20 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq121 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq110 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq110 X0 X1
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq121 (σ X1) (σ X0)
       grind)
    | exact superpose eq121 eq15
    | (have j1 := eq121 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq121 (τ X1) X0
       grind)
    | exact superpose eq121 eq17
    | (have j1 := eq121 (τ X1) X0
       grind)
    | exact resolve eq17 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq152 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq121 X1 X0
       grind)
    | exact superpose eq121 eq136
    | (have j0 := eq136 X0 X1
       have j1 := eq121 (σ X1) (σ X0)
       grind)
    | exact resolve eq136 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq833 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138
    | exact resolve eq138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq850 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq833
    | (have j0 := eq833 X0 X1
       grind)
    | exact resolve eq833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq1029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152 x y
       grind)
    | exact superpose eq152 eq16
    | (have j1 := eq152 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq152 x y
       grind)
    | exact resolve eq16 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq1067 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1029
  have eq1367 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq16
    | exact resolve eq16 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1368 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1067
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1067
       grind)
    | exact resolve eq12 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1369 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1368
  have eq1371 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1369
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1369
    | exact resolve eq1369 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq4622 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq850 y x
       have i₂ := eq1371
       grind)
    | exact superpose eq1371 eq850
    | (have j0 := eq850 y x
       grind)
    | exact resolve eq850 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq4624 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1371
       grind)
    | exact superpose eq1371 eq10
    | exact resolve eq10 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq4644 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4622
  have eq4652 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4624
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4624
    | exact resolve eq4624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4624
  have eq4653 : x = (M.op x y) := by
    first
    | (have r₁ := eq4644
       have r₂ := eq1367
       grind)
    | exact resolve eq4644 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq4644
  have eq4656 : x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq4652
       have r₂ := eq12 y x
       grind)
    | exact resolve eq4652 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4652
  have eq10121 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq136 x y
       have i₂ := eq4656
       grind)
    | exact superpose eq4656 eq136
    | (have j0 := eq136 x y
       grind)
    | exact resolve eq136 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq4656
  have eq10124 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10121
  have eq14743 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10124
       grind)
    | exact superpose eq10124 eq16
    | exact resolve eq16 eq10124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10124
  have eq14747 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq14743
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq14743
    | exact resolve eq14743 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653 eq14743
  have eq14748 : False := by grind
  exact eq14748

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  clear eq22
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq74 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq75 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq92 sF2 sF3
       grind)
    | exact superpose eq92 eq56
    | (have j1 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq114 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq112
    | exact resolve eq112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq114
    | exact resolve eq114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq44
    | exact resolve eq44 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq116
  have eq410 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq514 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq515 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq514
  have eq520 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq515 eq118
    | exact resolve eq118 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq524 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq520
  have eq531 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq524
       have r₂ := eq129
       grind)
    | exact resolve eq524 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq524
  have eq535 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq531 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq531
       grind)
    | exact resolve eq13 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq536 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq535
  have eq537 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq536
    | exact resolve eq536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq536
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq537 eq118
    | exact resolve eq118 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq537
  have eq612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq609
  have eq616 : y = (M.op x y) := by
    first
    | (have r₁ := eq612
       have r₂ := eq27
       grind)
    | exact resolve eq612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq618 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq616 eq20
    | exact resolve eq20 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq622 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq616 eq74
    | (have r₁ := eq74
       have r₂ := eq616
       grind)
    | exact resolve eq74 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq628 : y = (M.op y x) ∨ y = (k x y) := by grind
  clear eq622
  have eq636 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq618
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq618
    | exact resolve eq618 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq649 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq636 eq410
    | exact resolve eq410 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq654 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq649
       have r₂ := eq27
       grind)
    | exact resolve eq649 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq666 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq654 eq60
    | exact resolve eq60 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq654
  have eq668 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq616 eq666
    | exact resolve eq666 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq948 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq628
       have i₂ := eq668
       grind)
    | exact superpose eq668 eq628
    | exact resolve eq628 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq950 : y ≠ y ∨ (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq948
       grind)
    | exact resolve eq13 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq951 : (M.op x y) = (k x y) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq950
  have eq952 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq951
       have i₂ := eq668
       grind)
    | exact superpose eq668 eq951
    | exact resolve eq951 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq951
  have eq954 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq952
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq952
    | exact resolve eq952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq952
  have eq956 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq616 eq954
    | exact resolve eq954 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq954
  have eq957 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq956
  have eq962 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq957 eq15
    | exact resolve eq15 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq980 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq962
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq962
    | exact resolve eq962 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq962
  have eq986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq636 eq980
    | exact resolve eq980 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq980
  have eq990 : False := by grind
  exact eq990

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq21 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq21 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq83 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | (have j1 := eq25 (τ X0)
       grind)
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25
  have eq87 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | (have j0 := eq83 X0
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | (have j0 := eq87 X0
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq91 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq91 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq95 (σ X0)
       grind)
    | exact superpose eq95 eq15
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq155 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq155
    | exact resolve eq155 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq155
  have eq218 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq161 X0
       grind)
    | exact superpose eq161 eq63
    | exact resolve eq63 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq161
  have eq1041 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1054 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1041 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1041
    | (have j0 := eq1041 X0 X1
       grind)
    | exact resolve eq1041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1900 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq100 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq100 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq100 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1911 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1900
  have eq1934 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1911
       grind)
    | exact superpose eq1911 eq16
    | exact resolve eq16 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1935 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1911
       grind)
    | exact superpose eq1911 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1911
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1911
       grind)
    | exact resolve eq12 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1936 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1935
  have eq1938 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1936
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1936
    | exact resolve eq1936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq6816 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1054 y x
       have i₂ := eq1938
       grind)
    | exact superpose eq1938 eq1054
    | (have j0 := eq1054 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1054 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq1938
  have eq6842 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6816
  have eq6857 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6842
       have r₂ := eq1934
       grind)
    | exact resolve eq6842 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934 eq6842
  have eq14450 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6857
       grind)
    | exact superpose eq6857 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq6857
       grind)
    | exact resolve eq12 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14451 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14450
  have eq20088 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27 x y
       have i₂ := eq14451
       grind)
    | exact superpose eq14451 eq27
    | (have j0 := eq27 x y
       grind)
    | exact resolve eq27 eq14451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14451
  have eq20091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20088
  have eq24047 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq20091
       grind)
    | exact superpose eq20091 eq16
    | exact resolve eq16 eq20091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20091
  have eq40737 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24047
       have i₂ := eq6857
       grind)
    | exact superpose eq6857 eq24047
    | exact resolve eq24047 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857 eq24047
  have eq40738 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40737
  have eq40739 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq40738
  have eq58332 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40739
       grind)
    | exact superpose eq40739 eq10
    | exact resolve eq10 eq40739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40739
  have eq58370 : x = y ∨ x = y := by
    first
    | (have i₁ := eq58332
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58332
    | exact resolve eq58332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58332
  have eq58371 : x = y := by grind
  clear eq58370
  have eq67659 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58371
       grind)
    | exact superpose eq58371 eq16
    | exact resolve eq16 eq58371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58371
  have eq67660 : False := by grind
  exact eq67660

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pyx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  clear eq25 eq36
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq265 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq379 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq493 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq379 X0 (σ X0)
       grind)
    | (have i₁ := eq73 X0 X0
       have i₂ := eq379 (σ X0) X1
       grind)
    | exact superpose eq379 eq73
    | exact resolve eq73 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq520 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq538 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq265
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq12413 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq520 X0 (τ X1)
       grind)
    | exact superpose eq520 eq35
    | (have j1 := eq520 X0 (τ X1)
       grind)
    | exact resolve eq35 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq520
  have eq12500 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12413 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12413
    | (have j0 := eq12413 X0 X1
       grind)
    | exact resolve eq12413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12522 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12500 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12500
    | (have j0 := eq12500 X0 X1
       grind)
    | exact resolve eq12500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12500
  have eq13149 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522
  have eq13223 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13149 X1 (τ X0)
       have i₂ := eq538 X0 X0
       grind)
    | exact superpose eq538 eq13149
    | (have j0 := eq13149 X1 (τ X0)
       grind)
    | exact resolve eq13149 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq18807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq18808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18807
    | exact resolve eq18807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807
  have eq18819 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18808
       have r₂ := eq28
       grind)
    | exact resolve eq18808 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18808
  have eq18821 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq18819
       have i₂ := eq379 X0 sF3
       grind)
    | (have i₁ := eq18819
       have i₂ := eq379 sF3 x
       grind)
    | exact superpose eq379 eq18819
    | exact resolve eq18819 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq18930 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq18821 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18821
  have eq18931 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18930
  have eq18939 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq18931
       have i₂ := eq379 X0 sF2
       grind)
    | (have i₁ := eq18931
       have i₂ := eq379 sF2 x
       grind)
    | exact superpose eq379 eq18931
    | exact resolve eq18931 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq18996 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq18939 X1
       have i₂ := eq379 X0 y
       grind)
    | (have i₁ := eq18939 X1
       have i₂ := eq379 y X0
       grind)
    | exact superpose eq379 eq18939
    | (have j0 := eq18939 X1
       grind)
    | exact resolve eq18939 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq18939
  have eq19368 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq18996 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19370 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq19368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368
  have eq19385 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq19856 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq19385 X0
       grind)
    | exact superpose eq19385 eq44
    | (have j1 := eq19385 X0
       grind)
    | exact resolve eq44 eq19385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq19385
  have eq21434 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq19856 X0
       have i₂ := eq19370 X1
       grind)
    | exact superpose eq19370 eq19856
    | (have j0 := eq19856 X0
       have j1 := eq19370 X0
       grind)
    | exact resolve eq19856 eq19370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19370 eq19856
  have eq21543 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq21434 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21434
    | (have j0 := eq21434 X0 X0
       grind)
    | exact resolve eq21434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21434
  have eq21545 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq21543 X1 X1
       have j1 := eq13149 X1 (σ x)
       grind)
    | (have r₁ := eq21543 X0 X1
       have r₂ := eq13149 X0 (σ x)
       grind)
    | exact resolve eq21543 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13149 eq21543
  have eq21670 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21545 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21545
  have eq21671 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670
  have eq21721 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    grind
  have eq21725 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq21671 x
       grind)
    | exact superpose eq21671 eq63
    | exact resolve eq63 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21875 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21725
       have i₂ := eq21671 sF2
       grind)
    | exact superpose eq21671 eq21725
    | exact resolve eq21725 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21725
  have eq21928 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21875
       have i₂ := eq21671 sF2
       grind)
    | exact superpose eq21671 eq21875
    | exact resolve eq21875 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21875
  have eq21994 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq21928 eq13223
    | (have j0 := eq13223 (σ x) X0
       grind)
    | exact resolve eq13223 eq21928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223 eq21928
  have eq21997 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq21994 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21994
  have eq22013 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq21997
    | exact resolve eq21997 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21997
  have eq22034 : x = (σ x) := by
    first
    | (have i₁ := eq22013 x
       have i₂ := eq21671 x
       grind)
    | exact superpose eq21671 eq22013
    | exact resolve eq22013 eq21671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21671 eq22013
  have eq22043 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq22034 eq27
    | exact resolve eq27 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22368 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq22034 eq21721
    | exact resolve eq21721 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21721
  have eq22795 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq22368 y
       grind)
    | exact superpose eq22368 eq45
    | exact resolve eq45 eq22368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq22833 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq22034 eq22795
    | exact resolve eq22795 eq22034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22034 eq22795
  have eq22913 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq22833
       have i₂ := eq22368 sF3
       grind)
    | exact superpose eq22368 eq22833
    | exact resolve eq22833 eq22368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22368 eq22833
  have eq22984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22043 eq22913
    | exact resolve eq22913 eq22043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22043 eq22913
  have eq23031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22984
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22984
    | exact resolve eq22984 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22984
  have eq23064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq23031
    | exact resolve eq23031 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23031
  have eq23085 : False := by grind
  exact eq23085
