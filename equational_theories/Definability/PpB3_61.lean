import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyx_x_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  clear eq25
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
  have eq51 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X4) X5) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq14 X0 X4 X5 X6
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq101 y x
       grind)
    | exact superpose eq101 eq80
    | (have j1 := eq101 y x
       grind)
    | exact resolve eq80 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
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
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq124
    | exact resolve eq124 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq211 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X0 x X1
       have i₂ := eq57 X0 x X2
       grind)
    | (have i₁ := eq57 X0 X0 x
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq57 X0 X1 X5
       have i₂ := eq14 (M.op X0 X1) X2 X3 X4
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq125 eq101
    | (have j0 := eq101 (σ y) (σ x)
       grind)
    | exact resolve eq101 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq770
    | exact resolve eq770 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq774 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq771
       have r₂ := eq28
       grind)
    | exact resolve eq771 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq908 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq774 eq57
    | exact resolve eq57 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq774 eq14
    | exact resolve eq14 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq908 eq908
    | exact resolve eq908 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq908
    | (have j0 := eq908 (σ y)
       grind)
    | exact resolve eq908 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq929 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq951 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq930 eq908
    | exact resolve eq908 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq961 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq951 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq988 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27 eq910
    | (have j0 := eq910 (σ y) X0
       grind)
    | exact resolve eq910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1363 : ∀ X0 X1 : G, x ≠ (M.op (M.op (M.op x y) X0) X1) ∨ (k x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | (have j0 := eq70 x y X0 X1
       grind)
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1364 : ∀ X0 X1 : G, (σ x) ≠ (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq70
    | (have j0 := eq70 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq70 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1365 : ∀ X0 X1 : G, (σ x) ≠ (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq930 eq70
    | (have j0 := eq70 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq70 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1379 : ∀ X2 : G, (M.op x y) ≠ (M.op (M.op x x) X2) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq55 eq70
    | exact resolve eq70 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X2 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ x)) X2) ∨ (M.op (M.op (σ x) (σ x)) X2) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | exact superpose eq56 eq70
    | exact resolve eq70 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1382 : ∀ X0 X1 X2 X3 X4 X7 : G, (M.op X0 X4) ≠ (M.op (M.op (M.op (M.op X0 X1) X2) X3) X7) ∨ (M.op (M.op (M.op (M.op X0 X1) X2) X3) X7) = (k (M.op X0 X4) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4 X7
    first
    | (have i₁ := eq70 (M.op X0 X1) X2 X3 X3
       have i₂ := eq51 X0 X1 X2 X3 X4 x x
       grind)
    | (have i₁ := eq70 (M.op X0 X4) x x X3
       have i₂ := eq51 X0 X1 X2 X3 X4 x x
       grind)
    | exact superpose eq51 eq70
    | exact resolve eq70 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1395 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op (M.op X0 X1) X2) x x x
       have i₂ := eq52 X0 X1 X2 x x x
       grind)
    | exact superpose eq52 eq70
    | exact resolve eq70 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1403 : ∀ X2 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ x)) X2) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | exact superpose eq221 eq1381
    | (have j0 := eq1381 X2
       grind)
    | exact resolve eq1381 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1404 : ∀ X2 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | (have i₁ := eq1379 X2
       have i₂ := eq211 X2
       grind)
    | exact superpose eq211 eq1379
    | (have j0 := eq1379 X2
       grind)
    | exact resolve eq1379 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1408 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq56 eq1365
    | (have j0 := eq1365 X0 X1
       grind)
    | exact resolve eq1365 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq1409 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq56 eq1364
    | (have j0 := eq1364 X0 X1
       grind)
    | exact resolve eq1364 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1410 : ∀ X0 X1 : G, x ≠ (M.op x x) ∨ (k x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq55 eq1363
    | (have j0 := eq1363 X0 X1
       grind)
    | exact resolve eq1363 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1429 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq221 eq1403
    | exact resolve eq1403 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1430 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1404 x
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq1404
    | exact resolve eq1404 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1434 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq56 eq1408
    | exact resolve eq1408 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1435 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq56 eq1409
    | exact resolve eq1409 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1436 : (k x x) = (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq55 eq1410
    | exact resolve eq1410 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1452 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq101 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq1429
       have r₂ := eq101 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1429 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1453 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq101 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq1430
       have r₂ := eq101 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1430 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1457 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq101 (σ x) (σ x)
       grind)
    | (have r₁ := eq1434
       have r₂ := eq101 (σ x) (σ x)
       grind)
    | exact resolve eq1434 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq1458 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq101 (σ x) (σ x)
       grind)
    | (have r₁ := eq1435
       have r₂ := eq101 (σ x) (σ x)
       grind)
    | exact resolve eq1435 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq1459 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq101 x x
       grind)
    | (have r₁ := eq1436
       have r₂ := eq101 x x
       grind)
    | exact resolve eq1436 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq1464 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1457 eq50
    | exact resolve eq50 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1457
  have eq1752 : ∀ X0 : G, (k x x) = (τ (M.op (σ x) X0)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq947 eq1464
    | exact resolve eq1464 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1753 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq961 eq1464
    | exact resolve eq1464 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1766 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq1753
  have eq1767 : ∀ X0 : G, (k x x) = (τ (M.op (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1752 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq2030 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1453 eq135
    | exact resolve eq135 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1453
  have eq2170 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1459
       have i₂ := eq1766
       grind)
    | exact superpose eq1766 eq1459
    | exact resolve eq1459 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq2172 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq44
    | exact resolve eq44 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq2173 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq1458 eq2172
    | exact resolve eq2172 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458 eq2172
  have eq2174 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq211 X0
       have i₂ := eq2170
       grind)
    | exact superpose eq2170 eq211
    | exact resolve eq211 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2179 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x x x x
       have i₂ := eq2170
       grind)
    | exact superpose eq2170 eq14
    | exact resolve eq14 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq5112 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (σ y) X0) X1) X2) X3) = (M.op (σ x) X4) ∨ x = (M.op y y) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq774 eq462
    | exact resolve eq462 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq774
  have eq5344 : ∀ X3 X4 : G, (M.op (M.op (σ y) (σ y)) X3) = (M.op (σ x) X4) ∨ x = (M.op y y) := by
    intro X3 X4
    first
    | (have i₁ := eq5112 x x X3 X3 X4
       have i₂ := eq14 sF3 x x X3
       grind)
    | exact superpose eq14 eq5112
    | exact resolve eq5112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5112
  have eq5919 : ∀ X0 : G, (k x x) = (τ (M.op (M.op (σ y) (σ y)) X0)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq5344 eq1767
    | exact resolve eq1767 eq5344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq5936 : ∀ X0 : G, (k x x) = (τ (M.op (M.op (σ y) (σ y)) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq5919 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5919
  have eq5967 : ∀ X0 : G, (M.op x x) = (τ (M.op (M.op (σ y) (σ y)) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5936 X0
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq5936
    | exact resolve eq5936 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459 eq5936
  have eq12549 : ∀ X0 : G, (M.op x x) = (τ (M.op (σ x) X0)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq5344 eq5967
    | exact resolve eq5967 eq5344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5344 eq5967
  have eq12587 : ∀ X0 : G, (M.op x x) = (τ (M.op (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq12549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12549
  have eq12654 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq12587 eq15
    | exact resolve eq15 eq12587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12587
  have eq12787 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12654 eq961
    | (have j1 := eq12654 (σ y)
       grind)
    | exact resolve eq961 eq12654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq12654
  have eq12818 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq12787
  have eq33654 : ∀ X0 X2 X3 X4 X5 : G, (τ (M.op (σ x) (σ y))) ≠ (M.op (M.op (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X2) X3) X4) X5) ∨ (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X2) X3) X4) X5) ∨ x = (M.op y y) := by
    intro X0 X2 X3 X4 X5
    first
    | exact superpose eq2179 eq1382
    | exact resolve eq1382 eq2179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382 eq2179
  have eq34369 : ∀ X0 X2 X3 X4 X5 : G, (τ (M.op (σ x) (σ y))) ≠ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X2) X3) X4) X5) ∨ x = (M.op y y) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq33654 x X2 X3 X4 X5
       have i₂ := eq52 (τ sF4) x X2 X3 X4 X5
       grind)
    | exact superpose eq52 eq33654
    | (have j0 := eq33654 X0 X2 X3 X4 X5
       grind)
    | exact resolve eq33654 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33654
  have eq34661 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) ≠ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq34369 x x x x x
       have i₂ := eq52 (τ sF4) x x x x x
       grind)
    | exact superpose eq52 eq34369
    | exact resolve eq34369 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34369
  have eq34782 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq101 (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq34661
       have r₂ := eq101 (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq34661 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34661
  have eq67371 : (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) = (k (M.op (σ x) (σ y)) (σ (τ (M.op (σ x) (σ y))))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34782 eq35
    | exact resolve eq35 eq34782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq34782
  have eq67404 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67371
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq67371
    | exact resolve eq67371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67371
  have eq67431 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1452 eq67404
    | exact resolve eq67404 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq67404
  have eq67460 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2174 eq67431
    | exact resolve eq67431 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq67431
  have eq67512 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq67460
  have eq67594 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq67512 eq16
    | exact resolve eq16 eq67512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67512
  have eq67678 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq988 eq67594
    | exact resolve eq67594 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq67594
  have eq67717 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq67678
  have eq67724 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq67717
    | exact resolve eq67717 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq67717
  have eq67759 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq67724 eq55
    | exact resolve eq55 eq67724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq67724
  have eq68586 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67759 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67759
    | (have j0 := eq67759 y
       grind)
    | exact resolve eq67759 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67759
  have eq68925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12818
       have i₂ := eq68586
       grind)
    | exact superpose eq68586 eq12818
    | exact resolve eq12818 eq68586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12818 eq68586
  have eq69063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq68925
  have eq69131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq69063
    | exact resolve eq69063 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69063
  have eq69174 : x = (M.op y y) := by
    first
    | (have r₁ := eq69131
       have r₂ := eq28
       grind)
    | exact resolve eq69131 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69131
  have eq69233 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq455 y X1 x
       have i₂ := eq69174
       grind)
    | exact superpose eq69174 eq455
    | exact resolve eq455 eq69174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq69250 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 y y X2 X3 x x
       have i₂ := eq69174
       grind)
    | exact superpose eq69174 eq52
    | exact resolve eq52 eq69174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq69174
  have eq69328 : ∀ X3 : G, x = (M.op (M.op x x) X3) := by
    intro X3
    first
    | (have i₁ := eq69250 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq69250
    | exact resolve eq69250 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69250
  have eq69360 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq69328 x
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq69328
    | exact resolve eq69328 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq69328
  have eq69648 : ∀ X0 : G, (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq69233 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69233
    | (have j0 := eq69233 y X0
       grind)
    | exact resolve eq69233 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq69233
  have eq70471 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq69360 eq2030
    | exact resolve eq2030 eq69360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030 eq69360
  have eq70472 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq70471
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq70471
    | exact resolve eq70471 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq70471
  have eq70976 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2173
       have i₂ := eq69648 x
       grind)
    | exact superpose eq69648 eq2173
    | exact resolve eq2173 eq69648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173 eq69648
  have eq70977 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq70976
    | exact resolve eq70976 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq70976
  have eq70983 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq70977 eq221
    | exact resolve eq221 eq70977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq71512 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq70983 eq1395
    | exact resolve eq1395 eq70983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395 eq70983
  have eq71557 : ∀ X1 : G, (M.op (σ x) (σ x)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq56 eq71512
    | (have j0 := eq71512 X1
       grind)
    | exact resolve eq71512 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71512
  have eq71665 : ∀ X1 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq70977 eq71557
    | (have j0 := eq71557 X1
       grind)
    | exact resolve eq71557 eq70977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71557
  have eq71753 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq56 eq71665
    | exact resolve eq71665 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq71665
  have eq71804 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq70977 eq71753
    | exact resolve eq71753 eq70977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71753
  have eq71841 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq101 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq71804
       have r₂ := eq101 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq71804 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq71804
  have eq71864 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq70472 eq71841
    | exact resolve eq71841 eq70472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70472 eq71841
  have eq71924 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq71864 eq57
    | exact resolve eq57 eq71864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq71864
  have eq72005 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq70977 eq71924
    | exact resolve eq71924 eq70977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70977 eq71924
  have eq72168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72005 eq27
    | (have j1 := eq72005 (σ y)
       grind)
    | exact resolve eq27 eq72005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq72005
  have eq72311 : False := by grind
  exact eq72311

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_x_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq180 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 (M.op X0 X0) (M.op (M.op X0 X1) X2)
       have r₂ := eq16 X0 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq564 X0 X1 X2 X3
       have j1 := eq185 X0 X1 X2 X3
       grind)
    | (have r₁ := eq564 X0 X1 X2 X3
       have r₂ := eq185 X0 X1 X2 X3
       grind)
    | exact resolve eq564 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq564
  have eq589 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq580
       grind)
    | exact superpose eq580 eq40
    | exact resolve eq40 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq590 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq589
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq589
    | exact resolve eq589 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq592 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq590
    | exact resolve eq590 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq592 eq583
    | exact resolve eq583 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq592
  have eq609 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq602
       have r₂ := eq27
       grind)
    | exact resolve eq602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq616 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq609 eq16
    | exact resolve eq16 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 : G, (σ x) = (M.op (k X0 (σ x)) X1) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq616
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq616 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X2) ∨ x = (M.op y y) := by
    intro X2
    first
    | exact superpose eq616 eq16
    | exact resolve eq16 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq673 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (k X0 X1) X2) X3) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq587 X1 X0 X2 X3
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq587
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq587 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X2 : G, (M.op (M.op (σ x) (σ x)) X2) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | exact superpose eq180 eq587
    | exact resolve eq587 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq704 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq587 X0 x x x
       grind)
    | exact superpose eq587 eq16
    | exact resolve eq16 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (k X0 X0) X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X2) x X4 X5
       have i₂ := eq587 X0 X1 X2 x
       grind)
    | exact superpose eq587 eq16
    | exact resolve eq16 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X4) X5) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq709 X0 x x X4 X5
       have i₂ := eq16 X0 x x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq16 eq709
    | exact resolve eq709 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq727 : ∀ X2 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ x)) X2) := by
    intro X2
    first
    | (have i₁ := eq691 X2
       have i₂ := eq704 sF2
       grind)
    | exact superpose eq704 eq691
    | exact resolve eq691 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq739 : ∀ X0 X1 X2 X3 : G, (k X0 X0) = X1 ∨ (M.op (M.op (k X0 X1) X2) X3) = (k X1 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq675 X0 X1 X2 X3
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq675
    | (have j0 := eq675 X0 X1 X2 X3
       grind)
    | exact resolve eq675 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq740 : ∀ X0 X4 X5 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X4) X5) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq721 X0 X4 X5
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq721
    | exact resolve eq721 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq773 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq642 eq26
    | (have j1 := eq642 (σ y)
       grind)
    | exact resolve eq26 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq642 eq28
    | (have j0 := eq28 (σ x) (k X0 (σ x))
       grind)
    | exact resolve eq28 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq642
  have eq783 : ∀ X0 : G, (k (σ x) (σ x)) = (k X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq776 X0
       have i₂ := eq704 sF2
       grind)
    | exact superpose eq704 eq776
    | (have j0 := eq776 X0
       grind)
    | exact resolve eq776 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq784 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq773
       have i₂ := eq704 sF2
       grind)
    | exact superpose eq704 eq773
    | exact resolve eq773 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq795 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (k (σ x) (σ x)) = (k X0 (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq783 X0
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq783
    | (have j0 := eq783 X0
       grind)
    | exact resolve eq783 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq796 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq784
       have i₂ := eq704 y
       grind)
    | exact superpose eq704 eq784
    | exact resolve eq784 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq802 : ∀ X0 : G, x = (k y y) ∨ (σ x) = (k X0 X0) ∨ (k (σ x) (σ x)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq704 y
       grind)
    | exact superpose eq704 eq795
    | (have j0 := eq795 X0
       grind)
    | exact resolve eq795 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq806 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (k X0 X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq796 eq802
    | (have j0 := eq802 X0
       grind)
    | exact resolve eq802 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq802
  have eq1173 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq609 eq673
    | exact resolve eq673 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq673
  have eq1194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq1173
    | exact resolve eq1173 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1210 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1194
       have i₂ := eq704 y
       grind)
    | exact superpose eq704 eq1194
    | exact resolve eq1194 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq1210 eq806
    | (have j0 := eq806 (σ y)
       grind)
    | exact resolve eq806 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq1210
  have eq1252 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq1250
  have eq1272 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq1252 eq116
    | exact resolve eq116 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1282 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq1272
    | exact resolve eq1272 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1283 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1282
  have eq1494 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op (M.op (k X0 (σ x)) X1) X2) X3) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq637 eq16
    | (have j1 := eq637 X0 X1
       grind)
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq1506 : ∀ X0 X1 X2 X3 : G, x = (k y y) ∨ (σ x) = (M.op (M.op (M.op (k X0 (σ x)) X1) X2) X3) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1494 X0 X1 X2 X3
       have i₂ := eq704 y
       grind)
    | exact superpose eq704 eq1494
    | (have j0 := eq1494 X0 X1 X2 X3
       grind)
    | exact resolve eq1494 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1516 : ∀ X0 X1 X2 X3 : G, (σ x) = (k X0 X0) ∨ x = (k y y) ∨ (σ x) = (M.op (M.op (M.op (k X0 (σ x)) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1506 X0 X1 X2 X3
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq1506
    | (have j0 := eq1506 X0 X1 X2 X3
       grind)
    | exact resolve eq1506 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1526 : ∀ X0 X3 : G, (σ x) = (k X0 X0) ∨ x = (k y y) ∨ (σ x) = (M.op (k (σ x) (σ x)) X3) := by
    intro X0 X3
    first
    | exact superpose eq739 eq1516
    | (have j0 := eq1516 X0 x x X3
       have j1 := eq739 X0 (σ x) x X3
       grind)
    | exact resolve eq1516 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1516
  have eq1535 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k X0 X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq727 eq1526
    | (have j0 := eq1526 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq1526 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1541 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k X0 X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq1283 eq1535
    | (have j0 := eq1535 (σ y)
       grind)
    | exact resolve eq1535 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq1535
  have eq1563 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have j0 := eq1541 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1564 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by grind
  clear eq1563
  have eq1584 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1564 eq116
    | exact resolve eq116 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1564
  have eq1602 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq1584
    | exact resolve eq1584 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1584
  have eq1603 : x = (k y y) := by grind
  clear eq1602
  have eq1612 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1603
       grind)
    | exact superpose eq1603 eq41
    | exact resolve eq41 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1615 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1612
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1612
    | exact resolve eq1612 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1612
  have eq1618 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1615
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1615
    | exact resolve eq1615 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq3146 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq740 y x x
       have i₂ := eq1603
       grind)
    | exact superpose eq1603 eq740
    | exact resolve eq740 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq3162 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq1618 eq740
    | exact resolve eq740 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq3807 : ∀ X2 : G, (k x x) = (M.op x X2) := by
    intro X2
    first
    | (have i₁ := eq587 x x x X2
       have i₂ := eq3146 x x
       grind)
    | exact superpose eq3146 eq587
    | exact resolve eq587 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq3146
  have eq3961 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3162 eq198
    | (have j1 := eq3162 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq198 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq3162
  have eq4003 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3961
       have i₂ := eq704 sF4
       grind)
    | exact superpose eq704 eq3961
    | exact resolve eq3961 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq3961
  have eq4117 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3807 y
       grind)
    | exact superpose eq3807 eq18
    | (have j1 := eq3807 y
       grind)
    | exact resolve eq18 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3807
  have eq4153 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4117
       grind)
    | exact superpose eq4117 eq40
    | exact resolve eq40 eq4117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4117
  have eq4164 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4153
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4153
    | exact resolve eq4153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4153
  have eq4168 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq4164
    | exact resolve eq4164 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4164
  have eq4204 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq4168 eq727
    | exact resolve eq727 eq4168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq4213 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq4168 eq740
    | exact resolve eq740 eq4168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq4168
  have eq4226 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq4003 eq4204
    | exact resolve eq4204 eq4003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003 eq4204
  have eq4234 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x y)) X1) (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq4226 eq181
    | exact resolve eq181 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq4226
  have eq4257 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq4213 eq4234
    | exact resolve eq4234 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213 eq4234
  have eq4271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4257 eq26
    | (have j1 := eq4257 (σ y)
       grind)
    | exact resolve eq26 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4257
  have eq4306 : False := by grind
  exact eq4306

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyx_pxx_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq57 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23
  have eq106 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq123 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq678 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq390
    | exact resolve eq390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq1367 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 (σ X1) X1
       grind)
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 X0 (σ X1)
       grind)
    | exact superpose eq58 eq89
    | exact resolve eq89 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1407 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1367 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq7764 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 X2
       have i₂ := eq1407 X1 X0
       grind)
    | exact superpose eq1407 eq58
    | (have j1 := eq1407 X2 X0
       grind)
    | exact resolve eq58 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7850 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1407 X0 (τ X1)
       grind)
    | exact superpose eq1407 eq35
    | (have j1 := eq1407 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq7852 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq106
       have i₂ := eq1407 X0 y
       grind)
    | exact superpose eq1407 eq106
    | (have j1 := eq1407 X0 y
       grind)
    | exact resolve eq106 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7856 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X1 X1)
       have i₂ := eq1407 X0 X1
       grind)
    | exact superpose eq1407 eq16
    | (have j1 := eq1407 X0 X1
       grind)
    | exact resolve eq16 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq7880 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7852 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq7852
    | (have j0 := eq7852 X0
       grind)
    | exact resolve eq7852 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7852
  have eq7882 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7850 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7850
    | (have j0 := eq7850 X0 X1
       grind)
    | exact resolve eq7850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7850
  have eq7890 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7882 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7882
    | (have j0 := eq7882 X0 X1
       grind)
    | exact resolve eq7882 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7882
  have eq8124 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k (σ y) (σ y)) X2) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 X0 X2
       have i₂ := eq7880 X1
       grind)
    | exact superpose eq7880 eq57
    | (have j1 := eq7880 X1
       grind)
    | exact resolve eq57 eq7880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8126 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq7880 X0
       grind)
    | exact superpose eq7880 eq58
    | (have j1 := eq7880 X1
       grind)
    | exact resolve eq58 eq7880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq8493 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7890 X1 (τ X0)
       have i₂ := eq678 X0 X0
       grind)
    | exact superpose eq678 eq7890
    | (have j0 := eq7890 X1 (τ (k X0 X0))
       grind)
    | exact resolve eq7890 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8505 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X2 X1 X3
       have i₂ := eq7890 X2 X0
       grind)
    | exact superpose eq7890 eq57
    | (have j1 := eq7890 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq57 eq7890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq8507 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 X2
       have i₂ := eq7890 X1 X0
       grind)
    | exact superpose eq7890 eq58
    | (have j1 := eq7890 X2 X0
       grind)
    | exact resolve eq58 eq7890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8670 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7890 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7890
  have eq8722 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8670 X1 (τ X0)
       have i₂ := eq678 X0 X0
       grind)
    | exact superpose eq678 eq8670
    | (have j0 := eq8670 X1 (τ X0)
       grind)
    | exact resolve eq8670 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8670
  have eq9095 : ∀ X0 X1 : G, (k y y) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq8126 eq123
    | (have j1 := eq8126 X1 X1
       grind)
    | exact resolve eq123 eq8126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8126
  have eq9627 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq106
       have i₂ := eq8507 y X1 X0
       grind)
    | exact superpose eq8507 eq106
    | (have j1 := eq8507 y X1 x
       grind)
    | exact resolve eq106 eq8507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8507
  have eq51008 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X1)) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq678 X1 X1
       have i₂ := eq7856 X0 (τ X1)
       grind)
    | exact superpose eq7856 eq678
    | (have j1 := eq7856 X0 (τ X1)
       grind)
    | exact resolve eq678 eq7856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq7856
  have eq51103 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X1 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51008 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq51008
    | (have j0 := eq51008 X0 X1
       grind)
    | exact resolve eq51008 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51008
  have eq61618 : ∀ X0 X1 : G, (σ y) ≠ (M.op (k (σ y) (σ y)) X1) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq8124 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8124
  have eq61638 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq61618 X0 (k sF3 sF3)
       have i₂ := eq58 (k sF3 sF3) X1
       grind)
    | (have i₁ := eq61618 X0 (k sF3 sF3)
       have i₂ := eq58 X0 (k sF3 sF3)
       grind)
    | exact superpose eq58 eq61618
    | (have j0 := eq61618 X1 X1
       grind)
    | exact resolve eq61618 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61618
  have eq78287 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq8505 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq78357 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78287 X2 X1 (k X1 X1)
       have i₂ := eq58 (k X1 X1) X0
       grind)
    | (have i₁ := eq78287 X2 X1 (k X1 X1)
       have i₂ := eq58 X0 (k X1 X1)
       grind)
    | exact superpose eq58 eq78287
    | (have j0 := eq78287 X2 X1 X2
       grind)
    | (have r₁ := eq78287 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq58 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq78287 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq58 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq78287 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78287
  have eq84347 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq78357 x y y
       grind)
    | (have r₁ := eq117
       have r₂ := eq78357 y y x
       grind)
    | (have r₁ := eq117
       have r₂ := eq78357 x y x
       grind)
    | exact resolve eq117 eq78357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq84363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq84347 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq84347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84347
  have eq84364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq61638 x (σ y)
       grind)
    | (have r₁ := eq84363
       have r₂ := eq61638 (σ y) x
       grind)
    | (have r₁ := eq84363
       have r₂ := eq61638 (σ x) x
       grind)
    | exact resolve eq84363 eq61638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84363
  have eq84378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq84364
    | exact resolve eq84364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84364
  have eq84380 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq84378
       have r₂ := eq28
       grind)
    | exact resolve eq84378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84378
  have eq84382 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq84380
       have i₂ := eq58 sF3 x
       grind)
    | (have i₁ := eq84380
       have i₂ := eq58 X0 sF3
       grind)
    | exact superpose eq58 eq84380
    | exact resolve eq84380 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84385 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  have eq84443 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (σ y)) ∨ (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq84380 eq9627
    | (have j0 := eq9627 X0 X0
       grind)
    | exact resolve eq9627 eq84380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9627
  have eq84506 : (k (σ y) (σ y)) = (σ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq84443 y
       have j1 := eq78357 x y y
       grind)
    | (have r₁ := eq84443 x
       have r₂ := eq78357 x y x
       grind)
    | (have r₁ := eq84443 x
       have r₂ := eq78357 y y x
       grind)
    | exact resolve eq84443 eq78357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84443
  have eq84914 : ∀ X0 X1 : G, (k y y) = (τ y) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq9095 y X0
       have i₂ := eq84382 X1
       grind)
    | exact superpose eq84382 eq9095
    | (have j0 := eq9095 X0 X0
       have j1 := eq84382 X0
       grind)
    | exact resolve eq9095 eq84382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9095
  have eq84985 : ∀ X0 : G, (k y y) = (τ y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq84914 X0 X0
       have j1 := eq61638 X0 X0
       grind)
    | (have r₁ := eq84914 X0 x
       have r₂ := eq61638 X0 x
       grind)
    | (have r₁ := eq84914 X0 X0
       have r₂ := eq61638 X0 x
       grind)
    | exact resolve eq84914 eq61638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84914
  have eq86707 : (k y y) = (τ (σ (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq84506 eq123
    | exact resolve eq123 eq84506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq84506
  have eq86757 : (σ y) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86707
       have i₂ := eq16 sF3
       grind)
    | exact superpose eq16 eq86707
    | exact resolve eq86707 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86707
  have eq86788 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ (M.op X0 X0) = (τ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq8493 y X0
       have i₂ := eq86757
       grind)
    | exact superpose eq86757 eq8493
    | (have j0 := eq8493 (σ y) X0
       grind)
    | exact resolve eq8493 eq86757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8493
  have eq86794 : ∀ X0 : G, (τ (σ y)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq51103 X0 y
       have i₂ := eq86757
       grind)
    | exact superpose eq86757 eq51103
    | (have j0 := eq51103 X0 y
       grind)
    | exact resolve eq51103 eq86757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51103 eq86757
  have eq86814 : ∀ X0 : G, (τ (σ y)) = (τ (M.op X0 X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq86794 X0
       have j1 := eq78357 X0 y y
       grind)
    | (have r₁ := eq86794 X0
       have r₂ := eq78357 X0 y x
       grind)
    | (have r₁ := eq86794 X0
       have r₂ := eq78357 y y x
       grind)
    | exact resolve eq86794 eq78357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86794
  have eq86817 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = (τ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq86788
    | (have j0 := eq86788 X0
       grind)
    | exact resolve eq86788 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86788
  have eq86831 : ∀ X0 : G, y = (τ (M.op X0 X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq86814
    | exact resolve eq86814 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86814
  have eq86832 : ∀ X0 : G, (M.op X0 X0) = (τ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq86817 y
       have j1 := eq78357 X0 (τ y) X0
       grind)
    | (have r₁ := eq86817 X0
       have r₂ := eq78357 X0 y x
       grind)
    | (have r₁ := eq86817 X0
       have r₂ := eq78357 X0 (τ y) x
       grind)
    | (have r₁ := eq86817 X0
       have r₂ := eq78357 y y x
       grind)
    | exact resolve eq86817 eq78357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86817
  have eq86848 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (τ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq106
       have i₂ := eq84985 X0
       grind)
    | exact superpose eq84985 eq106
    | (have j1 := eq84985 X0
       grind)
    | exact resolve eq106 eq84985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq84985
  have eq86907 : ∀ X0 : G, y = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq86848 X0
       have i₂ := eq15 y
       grind)
    | exact superpose eq15 eq86848
    | (have j0 := eq86848 X0
       grind)
    | exact resolve eq86848 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86848
  have eq86969 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ (σ y)) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq86907 eq7764
    | (have j0 := eq7764 y X0 X2
       have j1 := eq86907 X0
       grind)
    | exact resolve eq7764 eq86907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764 eq86907
  have eq87005 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ (σ y)) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86969 X0 X1 X2
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq86969
    | (have j0 := eq86969 X0 X1 X0
       grind)
    | exact resolve eq86969 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq86969
  have eq87023 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq87005 X0 X1 X0
       have j1 := eq61638 X0 X0
       grind)
    | (have r₁ := eq87005 X0 X1 x
       have r₂ := eq61638 X0 X1
       grind)
    | (have r₁ := eq87005 X0 X1 X0
       have r₂ := eq61638 X0 X1
       grind)
    | exact resolve eq87005 eq61638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87005
  have eq88118 : (σ y) = (τ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq84380
       have i₂ := eq86832 sF3
       grind)
    | exact superpose eq86832 eq84380
    | exact resolve eq84380 eq86832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84380 eq86832
  have eq88124 : y = (M.op y y) ∨ (σ y) = (τ y) := by grind
  clear eq88118
  have eq88174 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq82 y x
       have i₂ := eq88124
       grind)
    | exact superpose eq88124 eq82
    | exact resolve eq82 eq88124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88124
  have eq93142 : ∀ X0 X1 : G, y = (σ (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq84382 X0
       have i₂ := eq87023 X1 y
       grind)
    | (have i₁ := eq84382 X0
       have i₂ := eq87023 y X1
       grind)
    | exact superpose eq87023 eq84382
    | (have j0 := eq84382 X0
       have j1 := eq87023 X0 X1
       grind)
    | exact resolve eq84382 eq87023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84382 eq87023
  have eq93166 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (σ (σ y)) := by
    intro X0
    first
    | (have j0 := eq93142 X0 X0
       have j1 := eq61638 X0 X0
       grind)
    | (have r₁ := eq93142 X0 x
       have r₂ := eq61638 X0 x
       grind)
    | (have r₁ := eq93142 X0 X0
       have r₂ := eq61638 X0 x
       grind)
    | exact resolve eq93142 eq61638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61638 eq93142
  have eq93395 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (σ (σ y)) := by
    intro X0
    grind
  clear eq93166
  have eq101866 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (τ y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq88174 x
       grind)
    | exact superpose eq88174 eq105
    | exact resolve eq105 eq88174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88174
  have eq101909 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (τ y) := by
    first
    | (have i₁ := eq101866
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101866
    | exact resolve eq101866 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101866
  have eq101942 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (τ y) := by
    first
    | exact superpose eq21 eq101909
    | exact resolve eq101909 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101909
  have eq105687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (τ y) ∨ y = (σ (σ y)) := by
    first
    | exact superpose eq93395 eq101942
    | exact resolve eq101942 eq93395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93395 eq101942
  have eq105715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (τ y) ∨ y = (σ (σ y)) := by
    first
    | exact superpose eq27 eq105687
    | exact resolve eq105687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105687
  have eq105745 : (σ y) = (τ y) ∨ y = (σ (σ y)) := by
    first
    | (have r₁ := eq105715
       have r₂ := eq28
       grind)
    | exact resolve eq105715 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105715
  have eq105752 : y = (σ (σ y)) ∨ y = (σ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq105745
       grind)
    | exact superpose eq105745 eq15
    | exact resolve eq15 eq105745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105745
  have eq105809 : y = (σ (σ y)) := by grind
  clear eq105752
  have eq105816 : (σ y) = (τ y) := by
    first
    | exact superpose eq105809 eq16
    | exact resolve eq16 eq105809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105809
  have eq125563 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq84385 eq8722
    | (have j0 := eq8722 (σ y) X0
       grind)
    | exact resolve eq8722 eq84385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84385
  have eq125584 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq125563
    | (have j0 := eq125563 X0
       grind)
    | exact resolve eq125563 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125563
  have eq125620 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq125584 X0
       grind)
    | (have r₁ := eq125584 X0
       have r₂ := eq86831 (σ y)
       grind)
    | exact resolve eq125584 eq86831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86831 eq125584
  have eq125636 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq125620
    | exact resolve eq125620 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq125620
  have eq125642 : y = (M.op y y) := by
    first
    | (have j0 := eq125636 y
       have j1 := eq78357 x y y
       grind)
    | (have r₁ := eq125636 x
       have r₂ := eq78357 x y x
       grind)
    | (have r₁ := eq125636 x
       have r₂ := eq78357 y y x
       grind)
    | exact resolve eq125636 eq78357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78357 eq125636
  have eq125646 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq125642
       have i₂ := eq58 y X0
       grind)
    | (have i₁ := eq125642
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq125642
    | exact resolve eq125642 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq125660 : (M.op y y) = (k y y) := by grind
  have eq125665 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq82 y x
       have i₂ := eq125642
       grind)
    | exact superpose eq125642 eq82
    | exact resolve eq82 eq125642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq125829 : y = (k y y) := by
    first
    | (have i₁ := eq125660
       have i₂ := eq125642
       grind)
    | exact superpose eq125642 eq125660
    | exact resolve eq125660 eq125642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125642 eq125660
  have eq127028 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq8722 y X0
       have i₂ := eq125829
       grind)
    | exact superpose eq125829 eq8722
    | (have j0 := eq8722 y X0
       grind)
    | exact resolve eq8722 eq125829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8722 eq125829
  have eq127042 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have j0 := eq127028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127028
  have eq127051 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq127042 X0
       have i₂ := eq105816
       grind)
    | exact superpose eq105816 eq127042
    | exact resolve eq127042 eq105816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105816 eq127042
  have eq127074 : y = (σ y) := by
    first
    | (have i₁ := eq127051 x
       have i₂ := eq125646 x
       grind)
    | exact superpose eq125646 eq127051
    | exact resolve eq127051 eq125646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125646 eq127051
  have eq127095 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq127074 eq27
    | exact resolve eq27 eq127074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq127996 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq125665 x
       grind)
    | exact superpose eq125665 eq105
    | exact resolve eq105 eq125665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq128068 : (σ (M.op x y)) = (k y (σ x)) := by
    first
    | exact superpose eq127074 eq127996
    | exact resolve eq127996 eq127074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127074 eq127996
  have eq128159 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq128068
       have i₂ := eq125665 sF2
       grind)
    | exact superpose eq125665 eq128068
    | exact resolve eq128068 eq125665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125665 eq128068
  have eq128235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127095 eq128159
    | exact resolve eq128159 eq127095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127095 eq128159
  have eq128294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128235
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq128235
    | exact resolve eq128235 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq128235
  have eq128326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq128294
    | exact resolve eq128294 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq128294
  have eq128343 : False := by grind
  exact eq128343

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq27 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X3 ∨ (M.op X3 X4) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 X3
       have i₂ := eq9 X3 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op (M.op X1 X2) X2)
       have i₂ := eq9 X0 X1 X2 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X4 X3
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X2) X3)
       have r₂ := eq9 (M.op (M.op (M.op X1 X2) X2) X3) X1 X2 X3
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X3) X4) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X1 X2 X3 X4
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2 X3
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1 x x x
       have j1 := eq27 X0 X1 x X0 X1
       grind)
    | (have r₁ := eq42 x X1 X0 X1 x
       have r₂ := eq27 X0 X1 x x x
       grind)
    | (have r₁ := eq42 (M.op (M.op (M.op X0 X1) X1) x) X1 x x x
       have r₂ := eq27 X0 X1 x (M.op (M.op (M.op x x) x) x) x
       grind)
    | (have r₁ := eq42 (M.op (M.op X0 X1) X1) X1 x x x
       have r₂ := eq27 X0 X1 (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1) x
       grind)
    | exact resolve eq42 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq42
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq60 (σ X0) (σ X1)
       grind)
    | exact superpose eq60 eq15
    | exact resolve eq15 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq81
    | exact resolve eq81 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq81
  have eq84 : False := by grind
  exact eq84

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pyy_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X1 (M.op x x) x X4
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq179 x X2
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq179 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180 x X1 X3
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq180 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq180
    | exact resolve eq180 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) X4) X5) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq16 x X3 X4 X5
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq16 (M.op X0 X0) X1 x X3
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq179 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq474 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1292 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1360 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X2 X0
       have i₂ := eq1292 X0 X1
       grind)
    | exact superpose eq1292 eq181
    | exact resolve eq181 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 (M.op X1 X1)
       have i₂ := eq1292 (σ X0) X1
       grind)
    | exact superpose eq1292 eq474
    | exact resolve eq474 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq1292 (τ X0) X1
       grind)
    | exact superpose eq1292 eq34
    | exact resolve eq34 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1452 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1360 X2 (M.op x x) X1
       have i₂ := eq279 x (M.op x x) X0
       grind)
    | exact superpose eq279 eq1360
    | exact resolve eq1360 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq474 X1 (M.op X2 X2)
       have i₂ := eq1360 (σ X1) X2 X0
       grind)
    | exact superpose eq1360 eq474
    | exact resolve eq474 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq1505 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 (M.op X2 X2)
       have i₂ := eq1360 (τ X1) X2 X0
       grind)
    | exact superpose eq1360 eq34
    | exact resolve eq34 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1508 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op x y)) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (M.op X1 X1)
       have i₂ := eq1360 sF0 X1 x
       grind)
    | exact superpose eq1360 eq37
    | exact resolve eq37 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1511 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k y (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (M.op X1 X1)
       have i₂ := eq1360 sF3 X1 x
       grind)
    | exact superpose eq1360 eq107
    | exact resolve eq107 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1360
  have eq1512 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1511 X0 x
       have i₂ := eq1391 y x
       grind)
    | exact superpose eq1391 eq1511
    | exact resolve eq1511 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391 eq1511
  have eq1515 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq1508 X0 x
       have i₂ := eq1392 sF1 x
       grind)
    | exact superpose eq1392 eq1508
    | exact resolve eq1508 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1508
  have eq1518 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1512 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1512
    | (have j0 := eq1512 X0
       grind)
    | exact resolve eq1512 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1521 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq28 eq1515
    | exact resolve eq1515 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1515
  have eq1559 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1518 X0
       have i₂ := eq1518 sF3
       grind)
    | exact superpose eq1518 eq1518
    | exact resolve eq1518 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1607 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1632 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1642 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1693 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1694 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1708 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1722 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1607 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1868 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1521 X0
       have i₂ := eq1521 sF0
       grind)
    | exact superpose eq1521 eq1521
    | exact resolve eq1521 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq5843 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1631
       grind)
    | exact superpose eq1631 eq39
    | exact resolve eq39 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1631
  have eq5844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5843
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5843
    | exact resolve eq5843 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5843
  have eq5846 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq5844
    | exact resolve eq5844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5844
  have eq9188 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1694 X1
       have i₂ := eq1708 X1 X0
       grind)
    | exact superpose eq1708 eq1694
    | (have j0 := eq1694 X1
       have j1 := eq1708 X1 X1
       grind)
    | (have r₁ := eq1694 (M.op X1 X1)
       have r₂ := eq1708 (M.op X1 X1) X1
       grind)
    | exact resolve eq1694 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694 eq1708
  have eq9218 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9188
  have eq9529 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq9558 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9529 X2 (σ (M.op X1 X1))
       have i₂ := eq1505 X0 (σ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1505 eq9529
    | (have j0 := eq9529 X2 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq9529 X0 (σ (M.op X0 X0))
       have r₂ := eq1505 X0 (σ (M.op X0 X0)) X0
       grind)
    | exact resolve eq9529 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9559 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9529 X2 (τ (M.op X1 X1))
       have i₂ := eq1504 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1504 eq9529
    | (have j0 := eq9529 X2 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq9529 X0 (τ (M.op X0 X0))
       have r₂ := eq1504 X0 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq9529 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504 eq9529
  have eq9564 : ∀ X1 X2 : G, (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq9559 x X1 X2
       grind)
    | (have r₁ := eq9559 x X1 X2
       have r₂ := eq1559 x X1
       grind)
    | (have r₁ := eq9559 X1 x X2
       have r₂ := eq1559 x X1
       grind)
    | exact resolve eq9559 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559 eq9559
  have eq9565 : ∀ X1 X2 : G, (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq9558 x X1 X2
       grind)
    | (have r₁ := eq9558 x X1 X2
       have r₂ := eq1868 x X1
       grind)
    | (have r₁ := eq9558 X1 x X2
       have r₂ := eq1868 x X1
       grind)
    | exact resolve eq9558 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868 eq9558
  have eq9616 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (τ (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9564 x X3
       have i₂ := eq16 x X0 X1 X2
       grind)
    | (have i₁ := eq9564 (M.op (M.op X1 X2) X2) X2
       have i₂ := eq16 X0 X1 X2 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq16 eq9564
    | exact resolve eq9564 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9685 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X3) X4) = (τ (M.op X0 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq16 x X2 X3 X4
       have i₂ := eq9564 X0 x
       grind)
    | exact superpose eq9564 eq16
    | exact resolve eq16 eq9564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9700 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) = (M.op (τ (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq279 x X3 X1
       have i₂ := eq9564 X0 x
       grind)
    | exact superpose eq9564 eq279
    | exact resolve eq279 eq9564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq9743 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (k X2 (σ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1505 X1 X2 x
       have i₂ := eq9564 X0 x
       grind)
    | exact superpose eq9564 eq1505
    | exact resolve eq1505 eq9564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq9816 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260 (M.op sF4 sF3) X1 x
       have i₂ := eq9564 X1 (M.op sF4 sF3)
       grind)
    | exact superpose eq9564 eq260
    | exact resolve eq260 eq9564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq9876 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9743 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9743
    | exact resolve eq9743 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9743
  have eq10929 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9565 x X1
       have i₂ := eq9565 X0 x
       grind)
    | exact superpose eq9565 eq9565
    | exact resolve eq9565 eq9565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11070 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9564 X2 x
       have i₂ := eq9565 X0 x
       grind)
    | exact superpose eq9565 eq9564
    | exact resolve eq9564 eq9565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9565
  have eq11780 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9564 X2 x
       have i₂ := eq10929 X0 x
       grind)
    | exact superpose eq10929 eq9564
    | exact resolve eq9564 eq10929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11834 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1452 (M.op sF4 sF3) X1 X2
       have i₂ := eq10929 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq10929 eq1452
    | exact resolve eq1452 eq10929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq13202 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (σ (M.op (τ (M.op X0 X0)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10929 x X2
       have i₂ := eq9816 X0 x X1
       grind)
    | (have i₁ := eq10929 (τ (M.op X0 X0)) X1
       have i₂ := eq9816 X0 X1 (τ (M.op X0 X0))
       grind)
    | exact superpose eq9816 eq10929
    | exact resolve eq10929 eq9816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13205 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (τ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11070 X2 x
       have i₂ := eq9816 X0 x X1
       grind)
    | (have i₁ := eq11070 X0 (τ (M.op X0 X0))
       have i₂ := eq9816 X0 X1 (τ (M.op X0 X0))
       grind)
    | exact superpose eq9816 eq11070
    | exact resolve eq11070 eq9816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9816 eq11070
  have eq14672 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 X2)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9876 X2 x X1
       have i₂ := eq10929 X0 x
       grind)
    | exact superpose eq10929 eq9876
    | exact resolve eq9876 eq10929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9876 eq10929
  have eq221430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5846 eq1632
    | exact resolve eq1632 eq5846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632 eq5846
  have eq221441 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq221430
       have r₂ := eq27
       grind)
    | exact resolve eq221430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221430
  have eq221524 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq221441 eq9564
    | exact resolve eq9564 eq221441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221441
  have eq221928 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq221524
    | exact resolve eq221524 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221524
  have eq222117 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq221928 x
       have j1 := eq9218 x x
       grind)
    | (have r₁ := eq221928 x
       have r₂ := eq9218 x x
       grind)
    | (have r₁ := eq221928 x
       have r₂ := eq9218 x x
       grind)
    | exact resolve eq221928 eq9218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9218 eq221928
  have eq222237 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 x X0 X1
       have i₂ := eq222117
       grind)
    | exact superpose eq222117 eq180
    | exact resolve eq180 eq222117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq222239 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq222117
       grind)
    | exact superpose eq222117 eq181
    | exact resolve eq181 eq222117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222117
  have eq222737 : ∀ X1 : G, x = (M.op x X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq222239 eq222237
    | exact resolve eq222237 eq222239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222237 eq222239
  have eq230615 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq222737 y
       grind)
    | exact superpose eq222737 eq18
    | (have j1 := eq222737 y
       grind)
    | exact resolve eq18 eq222737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222737
  have eq230907 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq230615
  have eq231127 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq230907 eq222
    | exact resolve eq222 eq230907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq231201 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq231127
    | (have j0 := eq231127 X1 X0
       grind)
    | exact resolve eq231127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231127
  have eq231238 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq230907 eq231201
    | exact resolve eq231201 eq230907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231201
  have eq231555 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq231238 eq26
    | (have j1 := eq231238 X0 (σ y)
       grind)
    | exact resolve eq26 eq231238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231640 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq231238 eq9700
    | exact resolve eq9700 eq231238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9700 eq231238
  have eq231869 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq230907 eq231640
    | exact resolve eq231640 eq230907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231640
  have eq231873 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq230907 eq231555
    | exact resolve eq231555 eq230907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231555
  have eq231894 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq231869
    | (have j0 := eq231869 X0 X1 X2
       grind)
    | exact resolve eq231869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231869
  have eq231912 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq230907 eq231894
    | exact resolve eq231894 eq230907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230907 eq231894
  have eq231930 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op (τ (σ x)) X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq231873 eq231912
    | exact resolve eq231912 eq231873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231912
  have eq231948 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op x X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq29 eq231930
    | exact resolve eq231930 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231930
  have eq231961 : ∀ X2 : G, (σ x) = (M.op x X2) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq231873 eq231948
    | exact resolve eq231948 eq231873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231948
  have eq231983 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq231873 eq181
    | exact resolve eq181 eq231873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq232050 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq231873 eq9564
    | exact resolve eq9564 eq231873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9564 eq231873
  have eq232425 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq232050
    | exact resolve eq232050 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq232050
  have eq232586 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq231983 eq232425
    | exact resolve eq232425 eq231983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231983 eq232425
  have eq232740 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq232586
  have eq232944 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq231961 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq231961 x
       grind)
    | exact superpose eq231961 eq18
    | (have j1 := eq231961 y
       grind)
    | exact resolve eq18 eq231961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231961
  have eq233434 : x = (M.op x y) := by
    first
    | (have r₁ := eq232944
       have r₂ := eq232740
       grind)
    | exact resolve eq232944 eq232740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232740 eq232944
  have eq233578 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq233434
       grind)
    | exact superpose eq233434 eq18
    | exact resolve eq18 eq233434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq233579 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq233434
       grind)
    | exact superpose eq233434 eq22
    | exact resolve eq22 eq233434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq233434
  have eq233590 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq233579 eq20
    | exact resolve eq20 eq233579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233579
  have eq233668 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq233578 eq178
    | exact resolve eq178 eq233578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq234305 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (σ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11780 x X1
       have i₂ := eq233668 x X0
       grind)
    | (have i₁ := eq11780 (M.op x y) x
       have i₂ := eq233668 X0 (M.op x y)
       grind)
    | exact superpose eq233668 eq11780
    | exact resolve eq11780 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780
  have eq234319 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (σ (σ (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11834 x X1 X2
       have i₂ := eq233668 x X0
       grind)
    | (have i₁ := eq11834 (M.op x y) X1 X2
       have i₂ := eq233668 X0 (M.op x y)
       grind)
    | exact superpose eq233668 eq11834
    | exact resolve eq11834 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11834
  have eq234373 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 X2)) = (σ (σ (σ (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14672 x X1 X2
       have i₂ := eq233668 x X0
       grind)
    | (have i₁ := eq14672 (M.op x y) X1 X2
       have i₂ := eq233668 X0 (M.op x y)
       grind)
    | exact superpose eq233668 eq14672
    | exact resolve eq14672 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14672
  have eq234474 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq277 X3 X4 X1 X1 X2
       have i₂ := eq233668 X1 X0
       grind)
    | (have i₁ := eq277 X0 X1 (M.op x y) X1 x
       have i₂ := eq233668 X0 X1
       grind)
    | exact superpose eq233668 eq277
    | exact resolve eq277 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq234481 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (τ (M.op (M.op (M.op (M.op x y) X0) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9616 X2 X2 X3 X1
       have i₂ := eq233668 X2 X0
       grind)
    | (have i₁ := eq9616 (M.op x y) X1 X2 X3
       have i₂ := eq233668 X0 X1
       grind)
    | exact superpose eq233668 eq9616
    | exact resolve eq9616 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9616
  have eq234482 : ∀ X0 X1 X2 X3 : G, (τ (M.op X3 X3)) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9685 X3 X1 X1 X2
       have i₂ := eq233668 X1 X0
       grind)
    | (have i₁ := eq9685 X0 (M.op x y) X1 x
       have i₂ := eq233668 X0 X1
       grind)
    | exact superpose eq233668 eq9685
    | exact resolve eq9685 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9685
  have eq234684 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13202 x (τ (M.op x x)) X1
       have i₂ := eq233668 (τ (M.op x x)) X0
       grind)
    | exact superpose eq233668 eq13202
    | exact resolve eq13202 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13202
  have eq234687 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (τ (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13205 x (τ (M.op x x)) X1
       have i₂ := eq233668 (τ (M.op x x)) X0
       grind)
    | exact superpose eq233668 eq13205
    | exact resolve eq13205 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13205
  have eq234754 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq233668 eq233578
    | exact resolve eq233578 eq233668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233578 eq233668
  have eq235049 : ∀ X0 : G, (σ (M.op x y)) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq234687 X0 x
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234687
    | exact resolve eq234687 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234687
  have eq235050 : ∀ X0 : G, (M.op x y) = (σ (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq234684 X0 x
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234684
    | exact resolve eq234684 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234684
  have eq235071 : ∀ X0 X1 X2 : G, (τ (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq234482 X0 X1 X2 x
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234482
    | exact resolve eq234482 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234482
  have eq235072 : ∀ X0 X2 X3 : G, (M.op x y) = (τ (M.op (M.op (M.op (M.op x y) X0) X2) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq234481 X0 x X2 X3
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234481
    | exact resolve eq234481 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234481
  have eq235074 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x y) X4) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq234474 X0 X1 X2 x X4
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234474
    | exact resolve eq234474 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234474
  have eq235165 : ∀ X0 X1 : G, (k X1 (M.op x y)) = (σ (σ (σ (M.op (M.op x y) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq234373 X0 X1 x
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234373
    | exact resolve eq234373 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234373
  have eq235218 : ∀ X0 X2 : G, (M.op x y) = (k X2 (σ (σ (M.op (M.op x y) X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq234319 X0 x X2
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234319
    | exact resolve eq234319 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234319
  have eq235230 : ∀ X0 : G, (τ (M.op x y)) = (σ (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq234305 X0 x
       have i₂ := eq234754 x
       grind)
    | exact superpose eq234754 eq234305
    | exact resolve eq234305 eq234754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234305 eq234754
  have eq235564 : ∀ X0 : G, (σ (M.op x y)) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq235049
    | (have j0 := eq235049 X0
       grind)
    | exact resolve eq235049 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235049
  have eq235569 : (M.op x y) = (τ (τ (M.op x y))) := by
    first
    | exact superpose eq235071 eq235072
    | exact resolve eq235072 eq235071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235072
  have eq235571 : ∀ X4 : G, (τ (M.op x y)) = (M.op (M.op x y) X4) := by
    intro X4
    first
    | exact superpose eq235071 eq235074
    | exact resolve eq235074 eq235071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235071 eq235074
  have eq235648 : ∀ X1 : G, (σ (M.op x y)) = (k X1 (M.op x y)) := by
    intro X1
    first
    | exact superpose eq235050 eq235165
    | exact resolve eq235165 eq235050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235165
  have eq235690 : ∀ X2 : G, (M.op x y) = (k X2 (M.op x y)) := by
    intro X2
    first
    | exact superpose eq235050 eq235218
    | exact resolve eq235218 eq235050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235218
  have eq235702 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq235050 eq235230
    | exact resolve eq235230 eq235050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235050 eq235230
  have eq235942 : ∀ X0 : G, (σ x) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq233590 eq235564
    | exact resolve eq235564 eq233590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233590 eq235564
  have eq236011 : ∀ X1 : G, (σ (M.op x y)) = (k X1 (M.op x y)) := by
    intro X1
    first
    | exact superpose eq20 eq235648
    | (have j0 := eq235648 X1
       grind)
    | exact resolve eq235648 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq235648
  have eq236238 : (σ x) = (τ (τ (M.op x y))) := by
    first
    | exact superpose eq235571 eq235942
    | exact resolve eq235942 eq235571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235942
  have eq236293 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq235690 eq236011
    | exact resolve eq236011 eq235690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235690 eq236011
  have eq236464 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq235569 eq236238
    | exact resolve eq236238 eq235569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235569 eq236238
  have eq236733 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq236464 eq26
    | exact resolve eq26 eq236464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq236464
  have eq236776 : (M.op (σ x) (σ y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq235571 eq236733
    | exact resolve eq236733 eq235571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235571 eq236733
  have eq236785 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq235702 eq236776
    | exact resolve eq236776 eq235702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235702 eq236776
  have eq236791 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq236785 eq27
    | exact resolve eq27 eq236785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq236785
  have eq236864 : False := by grind
  exact eq236864

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pyx_Equation4111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq59 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq112 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95
       have i₂ := eq60 sF2 x
       grind)
    | (have i₁ := eq95
       have i₂ := eq60 X0 sF2
       grind)
    | exact superpose eq60 eq95
    | exact resolve eq95 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq95
  have eq120 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq120
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq120
    | (have j1 := eq11 (M.op x x) x
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq128
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq128
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq134
    | exact resolve eq134 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq327 : ∀ X0 X1 : G, (M.op x x) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 x
       have i₂ := eq59 X0 x X1
       grind)
    | (have i₁ := eq112 (M.op X0 X0)
       have i₂ := eq59 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq112
    | exact resolve eq112 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq21811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq135 eq11
    | (have j0 := eq11 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq11 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq21812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq21811
    | exact resolve eq21811 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21811
  have eq21823 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq21812
       have r₂ := eq28
       grind)
    | exact resolve eq21812 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21812
  have eq21852 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21823 eq112
    | exact resolve eq112 eq21823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21823
  have eq21951 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq21852
    | exact resolve eq21852 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21852
  have eq21952 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21951
  have eq22127 : x = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq21952
       grind)
    | exact superpose eq21952 eq112
    | exact resolve eq112 eq21952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22139 : ∀ X0 : G, x = (τ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq327 x x
       have i₂ := eq21952
       grind)
    | exact superpose eq21952 eq327
    | exact resolve eq327 eq21952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq21952
  have eq22235 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22127
       grind)
    | exact superpose eq22127 eq15
    | exact resolve eq15 eq22127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22127
  have eq22268 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22235
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22235
    | exact resolve eq22235 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22235
  have eq22271 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq22268 eq30
    | exact resolve eq30 eq22268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22268
  have eq22378 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq22271
    | exact resolve eq22271 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22271
  have eq22379 : x = (σ x) ∨ x = y := by grind
  clear eq22378
  have eq22398 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq22379 eq27
    | exact resolve eq27 eq22379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27056 : x = (τ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22139 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22139
    | (have j0 := eq22139 y
       grind)
    | exact resolve eq22139 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27059 : x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq22398 eq22139
    | exact resolve eq22139 eq22398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22139 eq22398
  have eq27099 : x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27059
  have eq28159 : (σ x) = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27056 eq15
    | exact resolve eq15 eq27056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27056
  have eq28193 : (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq28159
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28159
    | exact resolve eq28159 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28159
  have eq28196 : y = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq28193 eq30
    | exact resolve eq30 eq28193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28193
  have eq28317 : x = y ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq28196
    | exact resolve eq28196 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28196
  have eq28318 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq28317
  have eq28403 : x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq28318 eq22379
    | exact resolve eq22379 eq28318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22379 eq28318
  have eq28426 : x = (M.op x y) ∨ x = y := by grind
  clear eq28403
  have eq28435 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28426 eq21
    | exact resolve eq21 eq28426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28426
  have eq28560 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq28435
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28435
    | exact resolve eq28435 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28435
  have eq29045 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27099 eq15
    | exact resolve eq15 eq27099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27099
  have eq29079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29045
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29045
    | exact resolve eq29045 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29045
  have eq29081 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29079 eq28
    | exact resolve eq28 eq29079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29079
  have eq29116 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29081
       have r₂ := eq28560
       grind)
    | exact resolve eq29081 eq28560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28560 eq29081
  have eq29119 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29116 eq30
    | exact resolve eq30 eq29116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29116
  have eq29244 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq29119
    | exact resolve eq29119 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29119
  have eq29245 : x = y := by grind
  clear eq29244
  have eq29264 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29245
       grind)
    | exact superpose eq29245 eq19
    | exact resolve eq19 eq29245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29265 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29245
       grind)
    | exact superpose eq29245 eq25
    | exact resolve eq25 eq29245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29245
  have eq29372 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29265
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29265
    | exact resolve eq29265 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29265
  have eq29387 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29372 eq27
    | exact resolve eq27 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29372
  have eq31313 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29387 eq112
    | exact resolve eq112 eq29387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq29387
  have eq31452 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31313
       have i₂ := eq29264
       grind)
    | exact superpose eq29264 eq31313
    | exact resolve eq31313 eq29264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29264 eq31313
  have eq31577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31452 eq15
    | exact resolve eq15 eq31452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31452
  have eq31621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq31577
    | exact resolve eq31577 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31577
  have eq31635 : False := by grind
  exact eq31635

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq391 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq404 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq402 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq402 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq402 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq412 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq403 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq403 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq403 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq403 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq415 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq391
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq391
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq418 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq412 X0 X1
       have j1 := eq404 X0 X1
       grind)
    | (have r₁ := eq412 X0 X1
       have r₂ := eq404 X0 X1
       grind)
    | exact resolve eq412 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq412
  have eq421 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq415
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq415
    | exact resolve eq415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq444 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq418 X0 (τ X1)
       grind)
    | exact superpose eq418 eq18
    | (have j1 := eq418 X0 (τ X1)
       grind)
    | exact resolve eq18 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq461 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq444 (τ X0) X1
       grind)
    | exact superpose eq444 eq17
    | (have j1 := eq444 (τ X0) X1
       grind)
    | exact resolve eq17 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq444
  have eq842 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq837
    | (have j0 := eq837 X0 X1
       grind)
    | exact resolve eq837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq855 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq858 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq920 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq858 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq858
    | (have j0 := eq858 X1 (σ X0)
       grind)
    | exact resolve eq858 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1303 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq920 X0 X0
       have i₂ := eq418 X0 (σ X0)
       grind)
    | exact superpose eq418 eq920
    | (have j0 := eq920 X1 X0
       have j1 := eq418 X0 (σ X1)
       grind)
    | exact resolve eq920 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq920
  have eq1339 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1303 X0 X1
       have j1 := eq461 X0 (σ X1)
       grind)
    | (have r₁ := eq1303 X0 X1
       have r₂ := eq461 X0 (σ X1)
       grind)
    | exact resolve eq1303 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq1303
  have eq1511 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1339 (σ X0) X1
       grind)
    | exact superpose eq1339 eq28
    | (have j1 := eq1339 (σ X0) X1
       grind)
    | exact resolve eq28 eq1339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1339
  have eq1522 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1511 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1511
    | (have j0 := eq1511 X0 X1
       grind)
    | exact resolve eq1511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1536 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1522 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1522
    | (have j0 := eq1522 X0 X1
       grind)
    | exact resolve eq1522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1545 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1536 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1536
    | (have j0 := eq1536 X0 X1
       grind)
    | exact resolve eq1536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1633 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1545 x y
       grind)
    | exact superpose eq1545 eq16
    | (have j1 := eq1545 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1545 x y
       grind)
    | exact resolve eq16 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1655 : x = (k x y) := by grind
  clear eq1633
  have eq1868 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq421
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq421
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq421 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1869 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq1868
  have eq1870 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1869
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq1869
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1869 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1871 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq1655
       grind)
    | exact superpose eq1655 eq1870
    | exact resolve eq1870 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq1872 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1871
       have i₂ := eq1655
       grind)
    | exact superpose eq1655 eq1871
    | exact resolve eq1871 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1873 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq421
       have i₂ := eq1872
       grind)
    | exact superpose eq1872 eq421
    | exact resolve eq421 eq1872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq1872
  have eq1885 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1873
  have eq1886 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq1655
       grind)
    | exact superpose eq1655 eq1885
    | exact resolve eq1885 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq1887 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1886
  have eq1889 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1887
       grind)
    | exact superpose eq1887 eq16
    | exact resolve eq16 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq1918 : (σ x) ≠ (σ x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1889
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1889
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1889 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by grind
  clear eq1918
  have eq1921 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1919
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq1919
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1919 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1922 : x = (M.op x y) := by
    first
    | (have i₁ := eq1921
       have i₂ := eq1655
       grind)
    | exact superpose eq1655 eq1921
    | exact resolve eq1921 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq1921
  have eq1923 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1889
       have i₂ := eq1922
       grind)
    | exact superpose eq1922 eq1889
    | exact resolve eq1889 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq1922
  have eq1937 : False := by grind
  exact eq1937

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq76 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq9
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq125 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq140 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq125
    | (have j0 := eq125 X0 X1
       grind)
    | exact resolve eq125 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq125
  have eq148 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq140 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq140 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq307 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq148 (σ X1) X0
       grind)
    | exact superpose eq148 eq15
    | (have j1 := eq148 (σ X1) X0
       grind)
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq364 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq307 (τ X0) X1
       grind)
    | exact superpose eq307 eq18
    | (have j1 := eq307 (τ X0) X1
       grind)
    | exact resolve eq18 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq307
  have eq864 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq364 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq364
    | exact resolve eq364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq922 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq864
    | (have j0 := eq864 X0 X1
       grind)
    | exact resolve eq864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq1499 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq317 x y
       grind)
    | exact superpose eq317 eq16
    | (have j1 := eq317 x y
       grind)
    | exact resolve eq16 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1857 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq922 x y
       grind)
    | exact superpose eq922 eq1499
    | (have j1 := eq922 (σ x) (σ y)
       grind)
    | (have r₁ := eq1499
       have r₂ := eq922 x y
       grind)
    | exact resolve eq1499 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1858 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1857
  have eq1863 : y ≠ y ∨ y = (k y x) ∨ (M.op x x) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1858
       grind)
    | exact superpose eq1858 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1858
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1858
       grind)
    | exact resolve eq13 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858
  have eq1865 : (M.op x x) = (M.op y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1863
  have eq13153 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1865
       grind)
    | exact superpose eq1865 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1865
       grind)
    | exact resolve eq12 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq13164 : y = (k y x) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13153
  have eq16312 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1517 x y
       have i₂ := eq13164
       grind)
    | exact superpose eq13164 eq1517
    | (have j0 := eq1517 x y
       grind)
    | exact resolve eq1517 eq13164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517 eq13164
  have eq16334 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq16312
  have eq16335 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16334
  have eq16445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq16335
       grind)
    | exact superpose eq16335 eq1499
    | exact resolve eq1499 eq16335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq16335
  have eq16468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16445
  have eq16469 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16468
  have eq16473 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16469
       grind)
    | exact superpose eq16469 eq16
    | exact resolve eq16 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16475 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq16469
       grind)
    | exact superpose eq16469 eq9
    | exact resolve eq9 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16476 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq16469
       grind)
    | exact superpose eq16469 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16469
       grind)
    | exact resolve eq13 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16483 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq16476
  have eq16490 : (σ y) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16483
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16483
    | exact resolve eq16483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16483
  have eq16491 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq16475
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq16475
    | exact resolve eq16475 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16475
  have eq16497 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16490
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq16490
    | exact resolve eq16490 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16490
  have eq16621 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76 y
       have i₂ := eq16491
       grind)
    | exact superpose eq16491 eq76
    | exact resolve eq76 eq16491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq16491
  have eq16655 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16621
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq16621
    | exact resolve eq16621 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16621
  have eq16848 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq16655
       grind)
    | exact superpose eq16655 eq77
    | (have j0 := eq77 y X0
       grind)
    | exact resolve eq77 eq16655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16655
  have eq19619 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16848 (σ x)
       have i₂ := eq16469
       grind)
    | exact superpose eq16469 eq16848
    | (have j0 := eq16848 (σ x)
       grind)
    | (have r₁ := eq16848 (σ x)
       have r₂ := eq16469
       grind)
    | exact resolve eq16848 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16848
  have eq19642 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
  clear eq19619
  have eq19662 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq19642
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19642
    | exact resolve eq19642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19642
  have eq19878 : (σ (M.op x x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq19662
       grind)
    | exact superpose eq19662 eq77
    | (have j0 := eq77 x (σ y)
       grind)
    | exact resolve eq77 eq19662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq19902 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq19878
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19878
    | exact resolve eq19878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19878
  have eq19927 : (σ (M.op x x)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq19902
       have i₂ := eq16469
       grind)
    | exact superpose eq16469 eq19902
    | exact resolve eq19902 eq16469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16469 eq19902
  have eq23015 : (σ (M.op x x)) = (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq19662
       have i₂ := eq16497
       grind)
    | exact superpose eq16497 eq19662
    | exact resolve eq19662 eq16497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16497 eq19662
  have eq23078 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq23015
       have r₂ := eq19927
       grind)
    | exact resolve eq23015 eq19927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19927 eq23015
  have eq23127 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq922 x y
       have i₂ := eq23078
       grind)
    | exact superpose eq23078 eq922
    | (have j0 := eq922 x y
       grind)
    | exact resolve eq922 eq23078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq23078
  have eq23237 : y = (M.op x y) := by
    first
    | (have r₁ := eq23127
       have r₂ := eq16473
       grind)
    | exact resolve eq23127 eq16473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23127
  have eq23444 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq16473
       have i₂ := eq23237
       grind)
    | exact superpose eq23237 eq16473
    | exact resolve eq16473 eq23237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16473 eq23237
  have eq23460 : False := by grind
  exact eq23460
