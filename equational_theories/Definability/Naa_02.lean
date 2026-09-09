import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pxy_Equation2666 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) := by
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
  have eq72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq213 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq218 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq700 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1049 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq700 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq700
    | (have j0 := eq700 x X0 y
       grind)
    | exact resolve eq700 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq700
    | (have j0 := eq700 (σ x) X0 (σ y)
       grind)
    | exact resolve eq700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq700 X0 X1 x
       grind)
    | exact superpose eq700 eq14
    | exact resolve eq14 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1054 X0 (M.op X0 X1)
       have i₂ := eq700 X0 X0 X1
       grind)
    | exact superpose eq700 eq1054
    | exact resolve eq1054 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq1219 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1049 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1049
    | (have j0 := eq1049 y
       grind)
    | exact resolve eq1049 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1392 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq1050
    | (have j0 := eq1050 (σ y)
       grind)
    | exact resolve eq1050 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1672 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq213 eq1118
    | exact resolve eq1118 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1678 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq218 eq1118
    | exact resolve eq1118 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1706 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1678
       have i₂ := eq1054 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1054 eq1678
    | exact resolve eq1678 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq1712 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1672
       have i₂ := eq1054 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1054 eq1672
    | exact resolve eq1672 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq1672
  have eq1753 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1706 eq218
    | exact resolve eq218 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1828 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1712 eq213
    | exact resolve eq213 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq33587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33587
    | exact resolve eq33587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33587
  have eq33600 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq33595
       have r₂ := eq28
       grind)
    | exact resolve eq33595 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33595
  have eq33602 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33600
    | exact resolve eq33600 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33600
  have eq33607 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq33602 eq72
    | (have r₁ := eq72
       have r₂ := eq33602
       grind)
    | exact resolve eq72 eq33602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq33602
  have eq33690 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq33607
  have eq33691 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq33690
  have eq33748 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq33691 eq89
    | exact resolve eq89 eq33691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq33751 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq33691 eq62
    | exact resolve eq62 eq33691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq33691
  have eq33761 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33748
  have eq33768 : x = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq33751
    | exact resolve eq33751 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33751
  have eq33776 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq33768
       have r₂ := eq71
       grind)
    | exact resolve eq33768 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq33768
  have eq33916 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq33776
       grind)
    | exact superpose eq33776 eq49
    | exact resolve eq49 eq33776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq33776
  have eq33946 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33916
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33916
    | exact resolve eq33916 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33916
  have eq34001 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq33946 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq33946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33946
  have eq34009 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34001
  have eq34016 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq34009
    | exact resolve eq34009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34009
  have eq34024 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq34016
    | exact resolve eq34016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34016
  have eq34027 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq33761
       grind)
    | exact superpose eq33761 eq52
    | exact resolve eq52 eq33761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33761
  have eq34170 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq34027
    | exact resolve eq34027 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34027
  have eq34879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34024 eq34170
    | exact resolve eq34170 eq34024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34879
  have eq34982 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq34949
       have r₂ := eq28
       grind)
    | exact resolve eq34949 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34949
  have eq35018 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34982 eq1753
    | exact resolve eq1753 eq34982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq35084 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1392 eq35018
    | exact resolve eq35018 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq35018
  have eq35097 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1706 eq35084
    | exact resolve eq35084 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706 eq35084
  have eq35974 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34982 eq35097
    | exact resolve eq35097 eq34982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34982 eq35097
  have eq36031 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35974
  have eq36662 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36031 eq34170
    | exact resolve eq34170 eq36031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34170 eq36031
  have eq36735 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36662
  have eq36821 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36735 eq30
    | exact resolve eq30 eq36735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36896 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq36821
    | exact resolve eq36821 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36821
  have eq36897 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq36896
  have eq36914 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq36897 eq29
    | exact resolve eq29 eq36897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36897
  have eq37039 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq36914
    | exact resolve eq36914 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36914
  have eq37101 : x = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq37039 eq1828
    | exact resolve eq1828 eq37039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq37180 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq37101
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq37101
    | exact resolve eq37101 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq37101
  have eq37239 : x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq1712 eq37180
    | exact resolve eq37180 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq37180
  have eq37400 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37039 eq37239
    | exact resolve eq37239 eq37039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37039 eq37239
  have eq37463 : x = (M.op x x) ∨ x = y := by grind
  clear eq37400
  have eq37740 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq37463
       grind)
    | exact superpose eq37463 eq52
    | exact resolve eq52 eq37463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq37463
  have eq37891 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37740
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37740
    | exact resolve eq37740 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37740
  have eq38330 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37891 eq34024
    | exact resolve eq34024 eq37891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34024 eq37891
  have eq38405 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38330
  have eq40174 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq38405 eq28
    | exact resolve eq28 eq38405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38405
  have eq40275 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40174
       have r₂ := eq36735
       grind)
    | exact resolve eq40174 eq36735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36735 eq40174
  have eq40304 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq40275 eq30
    | exact resolve eq30 eq40275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40275
  have eq40390 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq40304
    | exact resolve eq40304 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40304
  have eq40391 : x = y := by grind
  clear eq40390
  have eq40407 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq40391
       grind)
    | exact superpose eq40391 eq19
    | exact resolve eq19 eq40391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40408 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40391
       grind)
    | exact superpose eq40391 eq25
    | exact resolve eq25 eq40391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq40391
  have eq40559 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40408
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40408
    | exact resolve eq40408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40408
  have eq40589 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40559 eq27
    | exact resolve eq27 eq40559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40559
  have eq40878 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40589 eq70
    | exact resolve eq70 eq40589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq40589
  have eq41007 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40878
       have i₂ := eq40407
       grind)
    | exact superpose eq40407 eq40878
    | exact resolve eq40878 eq40407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40407 eq40878
  have eq41030 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41007 eq15
    | exact resolve eq15 eq41007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41007
  have eq41099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq41030
    | exact resolve eq41030 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq41030
  have eq41121 : False := by grind
  exact eq41121

/-- `Equation2675`: `x = ((x ◇ y) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2675 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2675 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2675.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
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
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq670
    | exact resolve eq670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq674 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq671
       have r₂ := eq27
       grind)
    | exact resolve eq671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq676 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq674
    | exact resolve eq674 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq678 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq676
    | exact resolve eq676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq682 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq678 eq51
    | (have r₁ := eq51
       have r₂ := eq678
       grind)
    | exact resolve eq51 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq685 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq682
  have eq777 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq685 eq55
    | exact resolve eq55 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq785 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq777
    | exact resolve eq777 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq777
  have eq789 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq785
       have r₂ := eq50
       grind)
    | exact resolve eq785 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq792 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq789
       grind)
    | exact superpose eq789 eq44
    | exact resolve eq44 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq789
       grind)
    | exact superpose eq789 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq794 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq793
  have eq796 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq794
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq794
    | exact resolve eq794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq797 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq796
  have eq798 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq792
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq792
    | exact resolve eq792 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq801 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq797
    | exact resolve eq797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq804 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq801 eq27
    | exact resolve eq27 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq801 eq51
    | exact resolve eq51 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq801 eq72
    | (have r₁ := eq72
       have r₂ := eq801
       grind)
    | exact resolve eq72 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq801
  have eq809 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq808
  have eq884 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq798 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq885 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq884
  have eq889 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq885
    | exact resolve eq885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq890 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq889
  have eq895 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq890
    | exact resolve eq890 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq897 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq895 eq27
    | exact resolve eq27 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq1006 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq809 eq55
    | exact resolve eq55 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq809
  have eq1017 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1006
    | exact resolve eq1006 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1006
  have eq1022 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1017
       have r₂ := eq71
       grind)
    | exact resolve eq1017 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1030 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1031 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1030
  have eq1033 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1031
    | exact resolve eq1031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1034 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1033
  have eq1039 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1034
    | exact resolve eq1034 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1034
  have eq1048 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1039 eq107
    | exact resolve eq107 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1056 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1039 eq805
    | (have r₁ := eq805
       have r₂ := eq1039
       grind)
    | exact resolve eq805 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq1039
  have eq1062 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1056
  have eq1063 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1062
  have eq1069 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1048
  have eq1264 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1069 eq1063
    | exact resolve eq1063 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq1069
  have eq1268 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1264
  have eq1272 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1268
       have r₂ := eq804
       grind)
    | exact resolve eq1268 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq1268
  have eq1338 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1272 eq20
    | exact resolve eq20 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1272 eq50
    | (have r₁ := eq50
       have r₂ := eq1272
       grind)
    | exact resolve eq50 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1355 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1340
  have eq1365 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1338
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1338
    | exact resolve eq1338 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1387 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq26
    | exact resolve eq26 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1406 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq897
    | (have r₁ := eq897
       have r₂ := eq1365
       grind)
    | exact resolve eq897 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq1412 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1406
  have eq1413 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1412
  have eq1433 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1413 eq27
    | exact resolve eq27 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1355
       grind)
    | exact superpose eq1355 eq44
    | exact resolve eq44 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1535 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1529
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1529
    | exact resolve eq1529 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1561 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1387 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1387
       grind)
    | exact resolve eq12 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1561
       have r₂ := eq1413
       grind)
    | exact resolve eq1561 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq1561
  have eq1574 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1573
       have r₂ := eq27
       grind)
    | exact resolve eq1573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1601 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq1535
    | exact resolve eq1535 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365 eq1535
  have eq1623 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1601
  have eq1647 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1623 eq1574
    | exact resolve eq1574 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574 eq1623
  have eq1651 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1647
  have eq1655 : x = (M.op x y) := by
    first
    | (have r₁ := eq1651
       have r₂ := eq1433
       grind)
    | exact resolve eq1651 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq1651
  have eq1659 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1655 eq20
    | exact resolve eq20 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1661 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq1655 eq50
    | exact resolve eq50 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1664 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq1655 eq71
    | (have r₁ := eq71
       have r₂ := eq1655
       grind)
    | exact resolve eq71 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1677 : y = (k x y) ∨ x = y := by grind
  clear eq1664
  have eq1687 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1659
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1659
    | exact resolve eq1659 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1688 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1687 eq26
    | exact resolve eq26 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1804 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1677
       grind)
    | exact superpose eq1677 eq44
    | exact resolve eq44 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1677
  have eq1813 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1687 eq1804
    | exact resolve eq1804 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq1817 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1813
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1813
    | exact resolve eq1813 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq1827 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1817 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1827
  have eq1831 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1688 eq1828
    | exact resolve eq1828 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1688 eq1831
    | exact resolve eq1831 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1837 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1834
       have r₂ := eq27
       grind)
    | exact resolve eq1834 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq1842 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1837 eq27
    | exact resolve eq27 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1837 eq51
    | (have r₁ := eq51
       have r₂ := eq1837
       grind)
    | exact resolve eq51 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1837
  have eq1857 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq1843
  have eq1866 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1687 eq1857
    | exact resolve eq1857 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq1888 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1866 eq1817
    | exact resolve eq1817 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq1889 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq1866 eq148
    | exact resolve eq148 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq1866
  have eq1892 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1888
  have eq1897 : (τ (σ (M.op x y))) = (k x y) ∨ x = y := by
    first
    | exact superpose eq1655 eq1889
    | exact resolve eq1889 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq1898 : x = y := by
    first
    | (have r₁ := eq1892
       have r₂ := eq1842
       grind)
    | exact resolve eq1892 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842 eq1892
  have eq1902 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1897
    | exact resolve eq1897 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1897
  have eq1905 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1655 eq1902
    | exact resolve eq1902 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq1902
  have eq1907 : x = (k x y) := by
    first
    | (have r₁ := eq1905
       have r₂ := eq1661
       grind)
    | exact resolve eq1905 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1905
  have eq1909 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1898
       grind)
    | exact superpose eq1898 eq24
    | exact resolve eq24 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1939 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1909
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1909
    | exact resolve eq1909 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq1949 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1687 eq1939
    | exact resolve eq1939 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1977 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1949 eq1688
    | exact resolve eq1688 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688 eq1949
  have eq2004 : x = (k x x) := by
    first
    | (have i₁ := eq1907
       have i₂ := eq1898
       grind)
    | exact superpose eq1898 eq1907
    | exact resolve eq1907 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898 eq1907
  have eq2006 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2004
       grind)
    | exact superpose eq2004 eq43
    | exact resolve eq43 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2004
  have eq2010 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1687 eq2006
    | exact resolve eq2006 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2011 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2010
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2010
    | exact resolve eq2010 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2010
  have eq2012 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1687 eq2011
    | exact resolve eq2011 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687 eq2011
  have eq2052 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2012 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012
  have eq2053 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2052
  have eq2072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1977 eq2053
    | exact resolve eq2053 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977 eq2053
  have eq2073 : False := by grind
  exact eq2073

/-- `Equation2679`: `x = ((x ◇ y) ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pxy_x_pxy_Equation2679 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2679 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2679.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X0)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 x) (M.op x X0))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq15
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq29 (τ X0)
       grind)
    | exact superpose eq29 eq17
    | exact resolve eq17 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq31
    | exact resolve eq31 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq33
    | exact resolve eq33 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | (have i₁ := eq14 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq83 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq83 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq101 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq105 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq55 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq55 X1 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq55 X0 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq116 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq105 X0 X1 X2
       have j1 := eq95 X0 X2 X2
       grind)
    | (have r₁ := eq105 X2 X1 X2
       have r₂ := eq95 X2 X1 X2
       grind)
    | (have r₁ := eq105 X0 X0 X1
       have r₂ := eq95 X0 X1 X0
       grind)
    | (have r₁ := eq105 X0 X1 X2
       have r₂ := eq95 X0 X1 X2
       grind)
    | exact resolve eq105 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq105
  have eq123 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq101
    | exact resolve eq101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq101 X0 (τ X1)
       grind)
    | exact superpose eq101 eq18
    | (have j1 := eq101 X0 (τ X1)
       grind)
    | exact resolve eq18 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq24
    | exact resolve eq24 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq158 X0 X1
       grind)
    | (have r₁ := eq155 X0 X1
       have r₂ := eq158 X0 X1
       grind)
    | (have r₁ := eq155 X0 (σ X0)
       have r₂ := eq158 X0 (σ X0)
       grind)
    | exact resolve eq155 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq158
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq92 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq92
    | (have j0 := eq92 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq92 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq92 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq181 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq186 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq181 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq181 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq181 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq187 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq186
    | (have j0 := eq186 X0 X1
       grind)
    | exact resolve eq186 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq187 (σ X0) (σ X1)
       grind)
    | exact superpose eq187 eq15
    | (have j1 := eq187 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq187 X0 (σ X1)
       grind)
    | exact superpose eq187 eq22
    | (have j1 := eq187 X0 (σ X1)
       grind)
    | exact resolve eq22 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq872 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq116 (σ x) (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq116 (σ x) X0 (σ y)
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 (σ x) (σ y) (σ y)
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq892 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq872 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq872
    | (have j0 := eq872 X0
       grind)
    | exact resolve eq872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq3497 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq141
    | exact resolve eq141 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3586 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3497 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3497
    | (have j0 := eq3497 X0 X1
       grind)
    | exact resolve eq3497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq4634 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137 x y
       grind)
    | exact superpose eq137 eq16
    | (have j1 := eq137 x y
       grind)
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq4831 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4634
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq4634
    | (have j1 := eq187 x y
       grind)
    | exact resolve eq4634 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq4832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4634
       have i₂ := eq3586 y x
       grind)
    | exact superpose eq3586 eq4634
    | (have j1 := eq3586 y x
       grind)
    | (have r₁ := eq4634
       have r₂ := eq3586 y x
       grind)
    | exact resolve eq4634 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586 eq4634
  have eq4833 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq4832
  have eq4834 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq4831
  have eq4964 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq4833
       grind)
    | exact superpose eq4833 eq10
    | exact resolve eq10 eq4833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4833
  have eq5002 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4964
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4964
    | exact resolve eq4964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4964
  have eq5003 : x = (k x y) := by
    first
    | (have j1 := eq142 x y
       grind)
    | (have r₁ := eq5002
       have r₂ := eq142 x y
       grind)
    | exact resolve eq5002 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq5002
  have eq5493 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ x))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22 X0 (M.op x y)
       have i₂ := eq4834
       grind)
    | exact superpose eq4834 eq22
    | exact resolve eq22 eq4834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834
  have eq5517 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (k (τ X0) x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5493 X0
       have i₂ := eq22 X0 x
       grind)
    | exact superpose eq22 eq5493
    | exact resolve eq5493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5493
  have eq16416 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq16803 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16416 X0 X1
       have i₂ := eq123 X0 X1
       grind)
    | exact superpose eq123 eq16416
    | (have j0 := eq16416 X0 X1
       grind)
    | exact resolve eq16416 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16416
  have eq16905 : (τ (M.op x y)) = (τ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16803 y x
       have i₂ := eq5003
       grind)
    | exact superpose eq5003 eq16803
    | (have j0 := eq16803 y x
       grind)
    | exact resolve eq16803 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16803
  have eq18163 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (τ x) (τ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq36 (M.op x y)
       have i₂ := eq16905
       grind)
    | exact superpose eq16905 eq36
    | exact resolve eq36 eq16905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16905
  have eq18228 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18163
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq18163
    | exact resolve eq18163 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18163
  have eq31797 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5517 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5517
    | exact resolve eq5517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq33072 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq29 (M.op x y)
       have i₂ := eq31797 (M.op x y)
       grind)
    | exact superpose eq31797 eq29
    | exact resolve eq29 eq31797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31797
  have eq102624 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq723 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq110702 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq102624 (τ X0) (τ X1)
       have i₂ := eq123 X1 X0
       grind)
    | exact superpose eq123 eq102624
    | (have j0 := eq102624 (τ X0) (τ X1)
       grind)
    | exact resolve eq102624 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq102624
  have eq110856 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110702 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq110702
    | (have j0 := eq110702 X0 X1
       grind)
    | exact resolve eq110702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110702
  have eq110893 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110856 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq110856
    | (have j0 := eq110856 X0 X1
       grind)
    | exact resolve eq110856 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110856
  have eq110923 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110893 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq110893
    | (have j0 := eq110893 X0 X1
       grind)
    | exact resolve eq110893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110893
  have eq110938 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110923 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq110923
    | (have j0 := eq110923 X0 X1
       grind)
    | exact resolve eq110923 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110923
  have eq110946 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110938 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq110938
    | (have j0 := eq110938 X0 X1
       grind)
    | exact resolve eq110938 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq110938
  have eq111486 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110946 x y
       have i₂ := eq5003
       grind)
    | exact superpose eq5003 eq110946
    | (have j0 := eq110946 x y
       grind)
    | exact resolve eq110946 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110946
  have eq418648 : (M.op x x) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18228
       have i₂ := eq33072
       grind)
    | exact superpose eq33072 eq18228
    | exact resolve eq18228 eq33072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18228 eq33072
  have eq419246 : (M.op x x) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq418648
  have eq419752 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq101 (M.op x y) x
       have i₂ := eq419246
       grind)
    | exact superpose eq419246 eq101
    | exact resolve eq101 eq419246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq419246
  have eq419834 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq419752
  have eq423853 : x = (M.op (M.op x x) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 x y
       have i₂ := eq419834
       grind)
    | exact superpose eq419834 eq24
    | exact resolve eq24 eq419834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419834
  have eq424746 : x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq423853
       grind)
    | exact superpose eq423853 eq24
    | exact resolve eq24 eq423853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423853
  have eq425038 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq424746
       have r₂ := eq111486
       grind)
    | exact resolve eq424746 eq111486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111486 eq424746
  have eq429142 : ∀ X0 : G, (M.op (σ x) X0) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq892 X0
       have i₂ := eq425038
       grind)
    | exact superpose eq425038 eq892
    | (have j0 := eq892 X0
       grind)
    | exact resolve eq892 eq425038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq429376 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq429142 X0
       have j1 := eq159 x X0
       grind)
    | (have r₁ := eq429142 x
       have r₂ := eq159 x x
       grind)
    | exact resolve eq429142 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq429142
  have eq429377 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq429376 X0
       have i₂ := eq5003
       grind)
    | exact superpose eq5003 eq429376
    | (have j0 := eq429376 X0
       grind)
    | exact resolve eq429376 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429376
  have eq449961 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq429377 (σ X0)
       grind)
    | exact superpose eq429377 eq15
    | exact resolve eq15 eq429377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429377
  have eq474123 : (σ x) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq449961
  have eq474136 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq474123
       have i₂ := eq5003
       grind)
    | exact superpose eq5003 eq474123
    | exact resolve eq474123 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003 eq474123
  have eq474137 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq474136
  have eq474957 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq474137
       grind)
    | exact superpose eq474137 eq16
    | exact resolve eq16 eq474137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475074 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq24 (σ x) (σ y)
       have i₂ := eq474137
       grind)
    | exact superpose eq474137 eq24
    | exact resolve eq24 eq474137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq474137
  have eq475451 : (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq475074
       have i₂ := eq34 x
       grind)
    | exact superpose eq34 eq475074
    | exact resolve eq475074 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475074
  have eq475533 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq474957
       have i₂ := eq425038
       grind)
    | exact superpose eq425038 eq474957
    | exact resolve eq474957 eq425038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425038 eq474957
  have eq479039 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq150 x
       have i₂ := eq475451
       grind)
    | exact superpose eq475451 eq150
    | exact resolve eq150 eq475451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq475451
  have eq479547 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq479039
       have i₂ := eq34 x
       grind)
    | exact superpose eq34 eq479039
    | exact resolve eq479039 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq479039
  have eq479643 : False := by grind
  exact eq479643

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pxy_x_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq69
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq283 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq284 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq124 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq995
    | exact resolve eq995 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq996
       have r₂ := eq27
       grind)
    | exact resolve eq996 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1001 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq999
    | exact resolve eq999 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1003 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1001 eq78
    | (have r₁ := eq78
       have r₂ := eq1001
       grind)
    | exact resolve eq78 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1008 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1001 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1016 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1003
  have eq1813 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1016 eq1008
    | (have j0 := eq1008 (σ y)
       grind)
    | (have r₁ := eq1008 (σ y)
       have r₂ := eq1016
       grind)
    | exact resolve eq1008 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq1016
  have eq1814 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1813
  have eq1815 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1814
  have eq1819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1815
    | exact resolve eq1815 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq124 eq1819
    | exact resolve eq1819 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1819 eq124
    | exact resolve eq124 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1819
  have eq1830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1826
  have eq1831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1824
  have eq1832 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1830
       have r₂ := eq27
       grind)
    | exact resolve eq1830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1833 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1831
       have r₂ := eq27
       grind)
    | exact resolve eq1831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1890 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1833
       grind)
    | exact superpose eq1833 eq72
    | exact resolve eq72 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1894 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x y) ∨ (k x X0) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1833
       grind)
    | exact superpose eq1833 eq13
    | (have j0 := eq13 x X0
       grind)
    | exact resolve eq13 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1903 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1890
    | exact resolve eq1890 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1999 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1832 eq60
    | exact resolve eq60 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1832
  have eq2005 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq1999
    | exact resolve eq1999 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2032 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq2005
       grind)
    | exact superpose eq2005 eq77
    | (have r₁ := eq77
       have r₂ := eq2005
       grind)
    | exact resolve eq77 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq2033 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq2005
       grind)
    | exact superpose eq2005 eq72
    | exact resolve eq72 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2045 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq2032
  have eq2046 : (M.op x y) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq2045
  have eq2047 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq2033
    | exact resolve eq2033 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq2103 : y = (M.op (M.op (M.op x y) y) y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq2046
       grind)
    | exact superpose eq2046 eq55
    | exact resolve eq55 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq4292 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1894 y
       have i₂ := eq2046
       grind)
    | exact superpose eq2046 eq1894
    | (have j0 := eq1894 y
       grind)
    | (have r₁ := eq1894 y
       have r₂ := eq2046
       grind)
    | exact resolve eq1894 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq2046
  have eq4300 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq4292
  have eq4304 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4300
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4300
    | exact resolve eq4300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4300
  have eq4308 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4304
       grind)
    | exact superpose eq4304 eq44
    | exact resolve eq44 eq4304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4304
  have eq4311 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq4308
    | exact resolve eq4308 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4308
  have eq4318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq4311 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311
  have eq4322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq4318
    | exact resolve eq4318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4318
  have eq4325 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq4322
       have r₂ := eq27
       grind)
    | exact resolve eq4322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4322
  have eq4327 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq4325
    | exact resolve eq4325 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325
  have eq4336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq4327 eq2047
    | exact resolve eq2047 eq4327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047 eq4327
  have eq4377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4336
  have eq4383 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4377
       have r₂ := eq27
       grind)
    | exact resolve eq4377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4377
  have eq4389 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4383
       grind)
    | exact superpose eq4383 eq44
    | exact resolve eq44 eq4383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383
  have eq4393 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4389
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4389
    | exact resolve eq4389 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389
  have eq4524 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4393 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq4393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4393
  have eq4529 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4524
    | exact resolve eq4524 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4524
  have eq4532 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4529
    | exact resolve eq4529 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529
  have eq4540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4532 eq1903
    | exact resolve eq1903 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532
  have eq4580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4540
  have eq4584 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4580
       have r₂ := eq27
       grind)
    | exact resolve eq4580 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4597 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4584 eq284
    | exact resolve eq284 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq4641 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4597
    | exact resolve eq4597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597
  have eq4659 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4584 eq4641
    | exact resolve eq4641 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584 eq4641
  have eq4675 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4659
  have eq4737 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4675 eq1903
    | exact resolve eq1903 eq4675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903 eq4675
  have eq4780 : (σ (M.op x y)) = (σ x) := by grind
  clear eq4737
  have eq4846 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4780 eq26
    | exact resolve eq26 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4847 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq4780 eq28
    | exact resolve eq28 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4893 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq4847
    | exact resolve eq4847 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4847
  have eq4915 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq4893 eq283
    | exact resolve eq283 eq4893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq4937 : y = (M.op (M.op x y) y) ∨ x = (k x y) := by
    first
    | exact superpose eq4893 eq2103
    | exact resolve eq2103 eq4893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq4949 : y = (M.op (M.op x y) y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4937
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4937
    | exact resolve eq4937 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937
  have eq4956 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq4915
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4915
    | exact resolve eq4915 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq4965 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4893 eq4949
    | exact resolve eq4949 eq4893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949
  have eq4966 : x = (M.op x x) := by
    first
    | exact superpose eq4893 eq4956
    | exact resolve eq4956 eq4893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4970 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4965
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4965
    | exact resolve eq4965 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4965
  have eq4973 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq4893 eq4970
    | exact resolve eq4970 eq4893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4893 eq4970
  have eq4998 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq4966
       grind)
    | exact superpose eq4966 eq72
    | exact resolve eq72 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq4966
  have eq5039 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4780 eq4998
    | exact resolve eq4998 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4998
  have eq5043 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5039
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5039
    | exact resolve eq5039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5045 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4780 eq5043
    | exact resolve eq5043 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043
  have eq5643 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq4973
       grind)
    | exact superpose eq4973 eq44
    | exact resolve eq44 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4973
  have eq5646 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4780 eq5643
    | exact resolve eq5643 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643
  have eq5648 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5646
    | exact resolve eq5646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646
  have eq5649 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4780 eq5648
    | exact resolve eq5648 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5648
  have eq5652 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5649 eq85
    | (have j0 := eq85 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq85 eq5649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5649
  have eq5653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4846 eq5652
    | exact resolve eq5652 eq4846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652
  have eq5656 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq5653
       have r₂ := eq27
       grind)
    | exact resolve eq5653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5653
  have eq5659 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq4846 eq5656
    | exact resolve eq5656 eq4846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq5662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5045 eq5659
    | exact resolve eq5659 eq5045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5664 : x = y := by
    first
    | (have r₁ := eq5662
       have r₂ := eq27
       grind)
    | exact resolve eq5662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5662
  have eq5667 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5664
       grind)
    | exact superpose eq5664 eq24
    | exact resolve eq24 eq5664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5664
  have eq5732 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5667
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5667
    | exact resolve eq5667 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5667
  have eq5751 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4780 eq5732
    | exact resolve eq5732 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4780 eq5732
  have eq6036 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5751 eq4846
    | exact resolve eq4846 eq5751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4846 eq5751
  have eq6040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5045 eq6036
    | exact resolve eq6036 eq5045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5045 eq6036
  have eq6068 : False := by grind
  exact eq6068

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X2 ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq14 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X1 X2) X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       have j1 := eq12 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq30 X1 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq30 X1 X1 X2
       have r₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq110 : ∀ X0 X4 : G, (M.op X0 X4) = (k X0 X4) ∨ (M.op X4 X0) = X0 := by
    intro X0 X4
    first
    | (have i₁ := eq31 X0 (M.op (M.op (M.op (M.op x X0) (M.op x x)) x) X0) x
       have i₂ := eq21 X0 x x x
       grind)
    | exact superpose eq21 eq31
    | (have j0 := eq31 X4 x X0
       grind)
    | exact resolve eq31 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31
  have eq115 : ∀ X0 X4 : G, (M.op X0 X4) = (k X0 X4) := by
    intro X0 X4
    first
    | (have j0 := eq110 X0 X4
       have j1 := eq12 X0 X4
       grind)
    | (have r₁ := eq110 X0 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq110 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq282 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq115 (σ X0) (σ X1)
       grind)
    | exact superpose eq115 eq15
    | exact resolve eq15 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq282
    | exact resolve eq282 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq282
  have eq288 : False := by grind
  exact eq288

/-- `Equation2741`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxx_pyy_pyx_Equation2741 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2741 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2741.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X2) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X2)) ≠ X0 ∨ (M.op X2 X2) = (k X2 (M.op (M.op X1 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X1 X1) (M.op X0 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op (M.op X1 X1) (M.op X0 X2))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : x ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y y) := by
    first
    | exact superpose eq181 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq182 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq195 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq179 eq192
    | exact resolve eq192 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq192
  have eq198 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq202 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq198
    | (have j0 := eq198 X0
       grind)
    | exact resolve eq198 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq205 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq202 eq177
    | exact resolve eq177 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq209 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0
       have i₂ := eq205 sF0
       grind)
    | exact superpose eq205 eq205
    | exact resolve eq205 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq205 (M.op X0 X0)
       grind)
    | exact superpose eq205 eq16
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq209 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq209 X0 X1
       grind)
    | exact superpose eq209 eq13
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq209 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq209 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq209 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq209 (M.op X1 X1) X0
       grind)
    | exact superpose eq209 eq16
    | exact resolve eq16 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (σ x) ≠ (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have j0 := eq13 (σ y) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq304 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq249 X0 sF4
       grind)
    | exact superpose eq249 eq301
    | (have j0 := eq301 X0
       grind)
    | exact resolve eq301 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq307 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq304 x
       have i₂ := eq249 x sF4
       grind)
    | exact superpose eq249 eq304
    | exact resolve eq304 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq308 : (k (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq307
       have i₂ := eq205 sF3
       grind)
    | exact superpose eq205 eq307
    | exact resolve eq307 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq309 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq195 eq308
    | exact resolve eq308 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq308
  have eq433 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq517 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq433
    | exact resolve eq433 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq766 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq209 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq209 X0 X1
       grind)
    | exact superpose eq209 eq11
    | exact resolve eq11 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq767 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k X0 X0) ∨ (M.op (M.op x y) (M.op x y)) = X0 ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq205 X0
       grind)
    | (have i₁ := eq11 (M.op x y) (M.op x y)
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq11
    | exact resolve eq11 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq779 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq11
    | exact resolve eq11 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 X1 : G, (M.op (k X0 X1) X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq815 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq830 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq831 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k X0 X0) ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq767 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq832 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq766 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq849 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq780
       have i₂ := eq205 sF2
       grind)
    | exact superpose eq205 eq780
    | exact resolve eq780 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq850 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq830 X0
       have j1 := eq247 X0 (M.op x y)
       grind)
    | (have r₁ := eq830 X0
       have r₂ := eq247 X0 (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq830 X0
       have r₂ := eq247 X0 (M.op x y)
       grind)
    | exact resolve eq830 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq851 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq777
       have i₂ := eq205 x
       grind)
    | exact superpose eq205 eq777
    | exact resolve eq777 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq857 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq831 X0
       have j1 := eq247 (M.op x y) X0
       grind)
    | (have r₁ := eq831 X0
       have r₂ := eq247 (M.op x y) (k X0 X0)
       grind)
    | (have r₁ := eq831 x
       have r₂ := eq247 (M.op x y) x
       grind)
    | (have r₁ := eq831 (M.op X0 X0)
       have r₂ := eq247 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq831 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq858 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq832 X0 X1
       have j1 := eq247 X0 X1
       grind)
    | (have r₁ := eq832 X0 X1
       have r₂ := eq247 X0 (k X1 X1)
       grind)
    | (have r₁ := eq832 X0 X1
       have r₂ := eq247 X0 X1
       grind)
    | (have r₁ := eq832 X0 (M.op X0 X0)
       have r₂ := eq247 X0 (M.op X0 X0)
       grind)
    | exact resolve eq832 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq832
  have eq868 : (M.op x y) = (k y x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq851
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq851
    | exact resolve eq851 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq874 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq857 X0
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq857
    | exact resolve eq857 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq976 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq216
    | exact resolve eq216 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq874 X0
       have i₂ := eq874 sF0
       grind)
    | exact superpose eq874 eq874
    | exact resolve eq874 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq874 (σ X0)
       grind)
    | exact superpose eq874 eq10
    | exact resolve eq10 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq517 X0 X0
       have i₂ := eq874 (τ X0)
       grind)
    | exact superpose eq874 eq517
    | exact resolve eq517 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0
       have i₂ := eq858 sF0 X1
       grind)
    | exact superpose eq858 eq216
    | exact resolve eq216 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq858
  have eq1207 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq987 X0 (σ X1)
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq987 (σ X1) X0
       grind)
    | exact superpose eq987 eq10
    | exact resolve eq10 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (k X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X1 X1
       have i₂ := eq987 X0 (τ X1)
       grind)
    | (have i₁ := eq517 X1 X1
       have i₂ := eq987 (τ X1) X0
       grind)
    | exact superpose eq987 eq517
    | exact resolve eq517 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq1821 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq817 X1
       have i₂ := eq987 X0 X1
       grind)
    | (have i₁ := eq817 X1
       have i₂ := eq987 X1 X0
       grind)
    | exact superpose eq987 eq817
    | (have j0 := eq817 X1
       grind)
    | (have r₁ := eq817 (k X0 X0)
       have r₂ := eq987 X0 (k X0 X0)
       grind)
    | (have r₁ := eq817 (k X1 X1)
       have r₂ := eq987 (k X1 X1) X1
       grind)
    | exact resolve eq817 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq987
  have eq1836 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k (M.op x y) (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 X1
       have i₂ := eq850 X1
       grind)
    | exact superpose eq850 eq1821
    | (have j0 := eq1821 X0 X1
       grind)
    | (have r₁ := eq1821 (M.op x y) (M.op X0 X0)
       have r₂ := eq850 X0
       grind)
    | exact resolve eq1821 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq2377 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq868
       grind)
    | exact superpose eq868 eq39
    | exact resolve eq39 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq868
  have eq2378 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2377
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2377
    | exact resolve eq2377 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2380 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2378
    | exact resolve eq2378 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2380 eq849
    | exact resolve eq849 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2916 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2909
       have r₂ := eq27
       grind)
    | exact resolve eq2909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2920 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2916
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq2916
    | exact resolve eq2916 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916
  have eq2947 : ∀ X0 : G, (τ (σ x)) = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2920 eq1209
    | exact resolve eq1209 eq2920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920
  have eq2972 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq2947
    | exact resolve eq2947 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq2980 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq2972 (M.op x y)
       have j1 := eq1836 x x
       grind)
    | (have r₁ := eq2972 x
       have r₂ := eq1836 x x
       grind)
    | (have r₁ := eq2972 x
       have r₂ := eq1836 (M.op x y) x
       grind)
    | exact resolve eq2972 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836 eq2972
  have eq3005 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2980 eq999
    | exact resolve eq999 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3007 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2980 eq1091
    | exact resolve eq1091 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3008 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2980 eq1207
    | exact resolve eq1207 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq2980
  have eq3037 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3008 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3008
    | (have j0 := eq3008 X0
       grind)
    | exact resolve eq3008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq3038 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3005
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3005
    | exact resolve eq3005 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3053 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3038 eq309
    | (have r₁ := eq309
       have r₂ := eq3038
       grind)
    | exact resolve eq309 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3054 : (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3053
  have eq3056 : (k (σ y) (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3054
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq3054
    | exact resolve eq3054 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054
  have eq3237 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3007 y
       grind)
    | exact superpose eq3007 eq18
    | (have j1 := eq3007 y
       grind)
    | exact resolve eq18 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3275 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3237 eq27
    | exact resolve eq27 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3279 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3237 eq309
    | (have r₁ := eq309
       have r₂ := eq3237
       grind)
    | exact resolve eq309 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq3280 : (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3279
  have eq3282 : (k (σ y) (σ x)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3280
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq3280
    | exact resolve eq3280 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3986 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq976 X0
       have i₂ := eq3037 sF0
       grind)
    | exact superpose eq3037 eq976
    | exact resolve eq976 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037
  have eq4453 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3986 eq26
    | (have j1 := eq3986 (σ y)
       grind)
    | exact resolve eq26 eq3986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986
  have eq4498 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4453 eq27
    | exact resolve eq27 eq4453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq4842 : (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3056 eq2380
    | exact resolve eq2380 eq3056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq4851 : (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq4842
  have eq4868 : (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3282 eq2380
    | exact resolve eq2380 eq3282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380 eq3282
  have eq4877 : (σ (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4868
  have eq5309 : ∀ X0 : G, (σ x) ≠ (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ x) X0 (σ y)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq5337 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq5309 X0
       have i₂ := eq249 X0 sF4
       grind)
    | exact superpose eq249 eq5309
    | (have j0 := eq5309 X0
       grind)
    | exact resolve eq5309 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq5382 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5337 x
       have i₂ := eq249 x sF4
       grind)
    | exact superpose eq249 eq5337
    | exact resolve eq5337 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq5337
  have eq5422 : (k (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5382
       have i₂ := eq205 sF3
       grind)
    | exact superpose eq205 eq5382
    | exact resolve eq5382 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5382
  have eq5445 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (M.op x y) (M.op x y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5422
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq5422
    | exact resolve eq5422 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422
  have eq5886 : (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4851 eq1001
    | exact resolve eq1001 eq4851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5887 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq4851 eq1091
    | exact resolve eq1091 eq4851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4851
  have eq5941 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq5886
    | exact resolve eq5886 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886
  have eq5977 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq5941 eq999
    | exact resolve eq999 eq5941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941
  have eq6020 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq5977
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5977
    | exact resolve eq5977 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5977
  have eq6021 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq6020
  have eq7062 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4877 eq999
    | exact resolve eq999 eq4877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7064 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4877 eq1091
    | exact resolve eq1091 eq4877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq8199 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7062 eq1091
    | exact resolve eq1091 eq7062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7062
  have eq8904 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8199 y
       grind)
    | exact superpose eq8199 eq18
    | (have j1 := eq8199 y
       grind)
    | exact resolve eq18 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8199
  have eq8932 : (σ (M.op x y)) = (σ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8904
  have eq8951 : (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8932 eq15
    | exact resolve eq15 eq8932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8932
  have eq8981 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq8951
    | exact resolve eq8951 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8951
  have eq8984 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8981 eq28
    | exact resolve eq28 eq8981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8996 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8981 eq3275
    | exact resolve eq3275 eq8981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq9013 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8996
  have eq10921 : ∀ X0 : G, x = (σ x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq999 X0
       have i₂ := eq5887 (k X0 X0)
       grind)
    | exact superpose eq5887 eq999
    | (have j1 := eq5887 X0
       grind)
    | exact resolve eq999 eq5887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq11000 : ∀ X0 : G, x = (σ x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq10921 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10921
    | (have j0 := eq10921 X0
       grind)
    | exact resolve eq10921 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10921
  have eq11001 : ∀ X0 : G, x = (σ x) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq11000 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11000
  have eq11030 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6021 eq11001
    | exact resolve eq11001 eq6021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6021 eq11001
  have eq11056 : x = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq11030 eq181
    | exact resolve eq181 eq11030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11129 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  have eq11131 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9013 eq11129
    | exact resolve eq11129 eq9013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9013 eq11129
  have eq11132 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq11131
  have eq13648 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1091 X0 X1
       have i₂ := eq7064 (k X0 X0)
       grind)
    | exact superpose eq7064 eq1091
    | (have j1 := eq7064 X1
       grind)
    | exact resolve eq1091 eq7064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7064
  have eq13733 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op (M.op x y) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8981 eq13648
    | (have j0 := eq13648 X0 X1
       grind)
    | exact resolve eq13648 eq8981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8981 eq13648
  have eq13776 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op (M.op x y) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11030 eq13733
    | (have j0 := eq13733 y X1
       have j1 := eq11030 X1
       grind)
    | exact resolve eq13733 eq11030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11030 eq13733
  have eq22496 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq13776 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq13776 eq26
    | (have j1 := eq13776 (σ y) X0
       grind)
    | exact resolve eq26 eq13776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13776
  have eq22541 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3237 eq22496
    | (have j0 := eq22496 X0
       grind)
    | exact resolve eq22496 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22496
  have eq22564 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22541 eq181
    | exact resolve eq181 eq22541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22541
  have eq22617 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22564 eq31
    | exact resolve eq31 eq22564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22564
  have eq22678 : x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq22617
    | exact resolve eq22617 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22617
  have eq22679 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22678
  have eq22695 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq22679
       grind)
    | exact superpose eq22679 eq24
    | exact resolve eq24 eq22679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22699 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq181
       have i₂ := eq22679
       grind)
    | exact superpose eq22679 eq181
    | exact resolve eq181 eq22679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22723 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22699
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq22699
    | exact resolve eq22699 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22699
  have eq22727 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq22695
    | exact resolve eq22695 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22695
  have eq22732 : (σ x) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11056 eq22723
    | exact resolve eq22723 eq11056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11056 eq22723
  have eq22761 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22727 eq4498
    | (have r₁ := eq4498
       have r₂ := eq22727
       grind)
    | exact resolve eq4498 eq22727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498
  have eq22802 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22761
  have eq22803 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22802
  have eq22814 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ x) := by
    first
    | exact superpose eq3038 eq22803
    | exact resolve eq22803 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038 eq22803
  have eq22828 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq3237 eq22814
    | exact resolve eq22814 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237 eq22814
  have eq22833 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22828
       have r₂ := eq11132
       grind)
    | exact resolve eq22828 eq11132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132 eq22828
  have eq22835 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22833 eq27
    | exact resolve eq27 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22840 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22833 eq5445
    | (have r₁ := eq5445
       have r₂ := eq22833
       grind)
    | exact resolve eq5445 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq22841 : (k (σ y) (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq22840
  have eq22851 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22727 eq22835
    | exact resolve eq22835 eq22727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22727 eq22835
  have eq22858 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22851
  have eq23065 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22732 eq1091
    | exact resolve eq1091 eq22732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22732
  have eq23914 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23065 eq26
    | (have j1 := eq23065 (σ y)
       grind)
    | exact resolve eq26 eq23065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23065
  have eq23957 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22833 eq23914
    | exact resolve eq23914 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23914
  have eq23969 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq23957
       have r₂ := eq22858
       grind)
    | exact resolve eq23957 eq22858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22858 eq23957
  have eq23975 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq23969
       grind)
    | exact superpose eq23969 eq22
    | exact resolve eq22 eq23969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23979 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq188
       have i₂ := eq23969
       grind)
    | exact superpose eq23969 eq188
    | (have r₁ := eq188
       have r₂ := eq23969
       grind)
    | exact resolve eq188 eq23969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq23983 : (k y (M.op x y)) = (M.op y y) ∨ x = y := by grind
  clear eq23979
  have eq23985 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq23983
       have i₂ := eq205 y
       grind)
    | exact superpose eq205 eq23983
    | exact resolve eq23983 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23983
  have eq23989 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq23975
    | exact resolve eq23975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23975
  have eq23991 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq23985
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq23985
    | exact resolve eq23985 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23985
  have eq24073 : (k (σ y) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq23991 eq36
    | exact resolve eq36 eq23991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq23991
  have eq24085 : (k (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq41 eq24073
    | exact resolve eq24073 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq24073
  have eq24087 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq24085
    | exact resolve eq24085 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24085
  have eq24089 : (k (M.op x y) (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq24087
       have i₂ := eq874 sF1
       grind)
    | exact superpose eq874 eq24087
    | exact resolve eq24087 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24087
  have eq24091 : (k (σ y) (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23989 eq24089
    | exact resolve eq24089 eq23989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24089
  have eq24093 : (k (σ y) (σ x)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22841 eq24091
    | exact resolve eq24091 eq22841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22841 eq24091
  have eq24105 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24093 eq849
    | exact resolve eq849 eq24093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq24127 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24105
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq24105
    | exact resolve eq24105 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24105
  have eq44000 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24127 eq999
    | exact resolve eq999 eq24127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq44001 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24127 eq1001
    | exact resolve eq1001 eq24127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24127
  have eq44274 : (σ x) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44000 eq1001
    | exact resolve eq1001 eq44000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44000
  have eq44410 : x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq44274
    | exact resolve eq44274 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44274
  have eq44432 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22833 eq44410
    | exact resolve eq44410 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44410
  have eq44438 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44432 eq15
    | exact resolve eq15 eq44432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44432
  have eq46015 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44001 eq1091
    | exact resolve eq1091 eq44001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44001
  have eq46162 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44438 eq46015
    | exact resolve eq46015 eq44438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44438 eq46015
  have eq47593 : x = y ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46162 eq181
    | exact resolve eq181 eq46162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46162
  have eq47637 : y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22833 eq47593
    | exact resolve eq47593 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47593
  have eq47638 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq47637
  have eq50943 : (σ x) = (M.op (k (M.op x y) (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24093 eq793
    | (have j0 := eq793 (σ x) (σ x)
       grind)
    | exact resolve eq793 eq24093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq24093
  have eq51100 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq976 eq50943
    | exact resolve eq50943 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq50943
  have eq51174 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51100
       have i₂ := eq205 sF2
       grind)
    | exact superpose eq205 eq51100
    | exact resolve eq51100 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51100
  have eq51229 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51174
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq51174
    | exact resolve eq51174 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51174
  have eq51257 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq51229
    | exact resolve eq51229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51229
  have eq53234 : (σ x) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51257 eq1001
    | exact resolve eq1001 eq51257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53235 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51257 eq1091
    | exact resolve eq1091 eq51257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq51257
  have eq53390 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq53234
    | exact resolve eq53234 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53234
  have eq53415 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22833 eq53390
    | exact resolve eq53390 eq22833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22833 eq53390
  have eq53418 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53415 eq27
    | exact resolve eq27 eq53415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53415
  have eq53435 : (σ x) ≠ (σ x) ∨ (M.op x y) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23989 eq53418
    | (have r₁ := eq53418
       have r₂ := eq23989
       grind)
    | exact resolve eq53418 eq23989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23989 eq53418
  have eq53442 : (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq53435
  have eq53444 : y = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq53442 eq31
    | exact resolve eq31 eq53442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53442
  have eq53507 : x = y ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq53444
    | exact resolve eq53444 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53444
  have eq53508 : (M.op x y) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq53507
  have eq53524 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq53508 eq26
    | exact resolve eq26 eq53508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53525 : x = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq53508 eq29
    | exact resolve eq29 eq53508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53677 : (M.op x y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq22679 eq53525
    | exact resolve eq53525 eq22679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53525
  have eq53696 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8984 eq53677
    | exact resolve eq53677 eq8984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8984 eq53677
  have eq53697 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq53696
  have eq53703 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53697 eq14
    | exact resolve eq14 eq53697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53720 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq53703
    | exact resolve eq53703 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53703
  have eq55600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53235 eq26
    | (have j1 := eq53235 (σ y)
       grind)
    | exact resolve eq26 eq53235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53235
  have eq55688 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55600 eq47638
    | exact resolve eq47638 eq55600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47638 eq55600
  have eq55702 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55688
  have eq55720 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq31 eq55702
    | exact resolve eq55702 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55702
  have eq55761 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq55720 eq27
    | exact resolve eq27 eq55720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55720
  have eq55776 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq53720 eq55761
    | exact resolve eq55761 eq53720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55761
  have eq55779 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) ∨ y = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq53508 eq55776
    | (have r₁ := eq55776
       have r₂ := eq53508
       grind)
    | exact resolve eq55776 eq53508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53508 eq55776
  have eq55780 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) ∨ y = (σ y) ∨ x = y := by grind
  clear eq55779
  have eq55781 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) ∨ x = y := by grind
  clear eq55780
  have eq55787 : y = (τ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq55781 eq31
    | exact resolve eq31 eq55781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq55781
  have eq55864 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq53697 eq55787
    | exact resolve eq55787 eq53697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53697 eq55787
  have eq55865 : y = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq55864
  have eq55882 : x = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq181
       have i₂ := eq55865
       grind)
    | exact superpose eq55865 eq181
    | exact resolve eq181 eq55865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq55865
  have eq55908 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22679 eq55882
    | exact resolve eq55882 eq22679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22679 eq55882
  have eq57107 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq55908 eq53524
    | exact resolve eq53524 eq55908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53524 eq55908
  have eq57129 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq57107
  have eq57165 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq57129 eq27
    | exact resolve eq27 eq57129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57129
  have eq57228 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq57165
       have r₂ := eq53720
       grind)
    | exact resolve eq57165 eq53720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53720 eq57165
  have eq57253 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq57228
  have eq57255 : x = y := by
    first
    | (have r₁ := eq57253
       have r₂ := eq23969
       grind)
    | exact resolve eq57253 eq23969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23969 eq57253
  have eq57265 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq57255
       grind)
    | exact superpose eq57255 eq18
    | exact resolve eq18 eq57255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57266 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq57255
       grind)
    | exact superpose eq57255 eq24
    | exact resolve eq24 eq57255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq57255
  have eq57297 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq57266
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57266
    | exact resolve eq57266 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq57266
  have eq57298 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq57265
       have i₂ := eq205 x
       grind)
    | exact superpose eq205 eq57265
    | exact resolve eq57265 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57265
  have eq57300 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq57298
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq57298
    | exact resolve eq57298 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57298
  have eq57302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57297 eq26
    | exact resolve eq26 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq57297
  have eq57369 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq57302
       have i₂ := eq205 sF2
       grind)
    | exact superpose eq205 eq57302
    | exact resolve eq57302 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq57302
  have eq57371 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq57369
       have i₂ := eq850 sF0
       grind)
    | exact superpose eq850 eq57369
    | exact resolve eq57369 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq57369
  have eq57373 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57300 eq57371
    | exact resolve eq57371 eq57300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57371
  have eq57382 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq57373 eq27
    | exact resolve eq27 eq57373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57373
  have eq57918 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq57300 eq37
    | exact resolve eq37 eq57300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq57932 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq57300 eq1001
    | exact resolve eq1001 eq57300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq57935 : ∀ X0 : G, (k X0 X0) = (τ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq57300 eq1209
    | exact resolve eq1209 eq57300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq57300
  have eq58053 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq57918
    | exact resolve eq57918 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq57918
  have eq58064 : (σ (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq58053
       have i₂ := eq874 sF1
       grind)
    | exact superpose eq874 eq58053
    | exact resolve eq58053 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq58053
  have eq58071 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq58064
       have i₂ := eq57935 sF0
       grind)
    | exact superpose eq57935 eq58064
    | exact resolve eq58064 eq57935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57935 eq58064
  have eq58075 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq57932 eq58071
    | exact resolve eq58071 eq57932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57932 eq58071
  have eq58077 : False := by grind
  exact eq58077

/-- `Equation2743`: `x = ((y ◇ y) ◇ (y ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2743 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2743 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2743.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq589
    | exact resolve eq589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq593 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq590
       have r₂ := eq27
       grind)
    | exact resolve eq590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq595 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq593
    | exact resolve eq593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq597 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq595
    | exact resolve eq595 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq610 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq597 eq67
    | (have r₁ := eq67
       have r₂ := eq597
       grind)
    | exact resolve eq67 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq597
  have eq615 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq610
  have eq629 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq615
       have r₂ := eq614
       grind)
    | exact resolve eq615 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq615
  have eq704 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq629 eq82
    | exact resolve eq82 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq712 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq704
    | exact resolve eq704 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq704
  have eq716 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq712
       have r₂ := eq66
       grind)
    | exact resolve eq712 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq719 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq716
       grind)
    | exact superpose eq716 eq75
    | exact resolve eq75 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq716
       grind)
    | exact superpose eq716 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq721 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq720
  have eq723 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq721
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq721
    | exact resolve eq721 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq724 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq723
  have eq725 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq719
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq719
    | exact resolve eq719 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq728 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq724
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq724
    | exact resolve eq724 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq732 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq728 eq51
    | (have r₁ := eq51
       have r₂ := eq728
       grind)
    | exact resolve eq51 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq734 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq732
  have eq740 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq725 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq741 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq740
  have eq745 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq741
    | exact resolve eq741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq745
  have eq751 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq746
    | exact resolve eq746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq796 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq751 eq27
    | exact resolve eq27 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq855 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq734 eq82
    | exact resolve eq82 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq866 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq855
    | exact resolve eq855 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq869 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq866
       have r₂ := eq50
       grind)
    | exact resolve eq866 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq875 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq876 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq875
  have eq878 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq876
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq876
    | exact resolve eq876 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq879 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq878
  have eq883 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq879
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq879
    | exact resolve eq879 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq879
  have eq928 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq883 eq20
    | exact resolve eq20 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq883 eq66
    | (have r₁ := eq66
       have r₂ := eq883
       grind)
    | exact resolve eq66 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq941 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq883
  have eq942 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq932
  have eq953 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq928
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq928
    | exact resolve eq928 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq953 eq796
    | (have r₁ := eq796
       have r₂ := eq953
       grind)
    | exact resolve eq796 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq953
  have eq1020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1017
  have eq1021 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1020
  have eq1041 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1021 eq51
    | (have r₁ := eq51
       have r₂ := eq1021
       grind)
    | exact resolve eq51 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1021
  have eq1043 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1041
  have eq1173 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1043 eq82
    | exact resolve eq82 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1043
  have eq1188 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1173
    | exact resolve eq1173 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1173
  have eq1191 : y = (k y x) := by
    first
    | (have r₁ := eq1188
       have r₂ := eq50
       grind)
    | exact resolve eq1188 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1188
  have eq1196 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1191
       grind)
    | exact superpose eq1191 eq75
    | exact resolve eq75 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1201 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1196
    | exact resolve eq1196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1196
  have eq1214 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1201 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1214
  have eq1217 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1215
    | exact resolve eq1215 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1217
    | exact resolve eq1217 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1217
  have eq1274 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1220 eq67
    | (have r₁ := eq67
       have r₂ := eq1220
       grind)
    | exact resolve eq67 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1277 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1220
  have eq1278 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1274
  have eq1279 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1201 eq1278
    | exact resolve eq1278 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq1278
  have eq1280 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1279
  have eq1333 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1280
       have r₂ := eq1277
       grind)
    | exact resolve eq1280 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq1280
  have eq1337 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1333 eq27
    | exact resolve eq27 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1333
  have eq2263 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq942
       have r₂ := eq941
       grind)
    | exact resolve eq942 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq2264 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2263
       have i₂ := eq1191
       grind)
    | exact superpose eq1191 eq2263
    | exact resolve eq2263 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191 eq2263
  have eq2265 : x = (M.op x y) := by
    first
    | (have r₁ := eq2264
       have r₂ := eq941
       grind)
    | exact resolve eq2264 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq2264
  have eq2267 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2265 eq20
    | exact resolve eq20 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2265
  have eq2297 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2267
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2267
    | exact resolve eq2267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2267
  have eq2299 : False := by grind
  exact eq2299

/-- `Equation2865`: `x = ((x ◇ (y ◇ x)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation2865 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2865 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2865.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq10
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq43
    | exact resolve eq43 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq49
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
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
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq63 sF3
       grind)
    | exact superpose eq63 eq96
    | exact resolve eq96 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq100
    | exact resolve eq100 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq100
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq141 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq16
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq703 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq702
  have eq828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq703 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq703 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq18840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18840
    | exact resolve eq18840 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18840
  have eq18852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq18841
       have r₂ := eq27
       grind)
    | exact resolve eq18841 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18841
  have eq18856 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18852
    | exact resolve eq18852 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18852
  have eq18858 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18856
    | exact resolve eq18856 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18856
  have eq18873 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18858 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18858
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18858
       grind)
    | exact resolve eq13 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858
  have eq23729 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq18873
    | (have j0 := eq18873 (σ x)
       grind)
    | (have r₁ := eq18873 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq18873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18873
  have eq23733 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq23729
  have eq23746 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23733 eq109
    | exact resolve eq109 eq23733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23733
  have eq23775 : (M.op x x) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq68 eq23746
    | exact resolve eq23746 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq23746
  have eq24178 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq23775
       grind)
    | exact superpose eq23775 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq23775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23775
  have eq24179 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24178
  have eq24182 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24179
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24179
    | exact resolve eq24179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24179
  have eq24183 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24182
  have eq24200 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24183
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24183
    | exact resolve eq24183 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24183
  have eq24201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24200
  have eq24246 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24201 eq88
    | (have r₁ := eq88
       have r₂ := eq24201
       grind)
    | exact resolve eq88 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24270 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24246
  have eq32224 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24270 eq109
    | exact resolve eq109 eq24270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq24270
  have eq32261 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq141 eq32224
    | exact resolve eq32224 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq32224
  have eq32267 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq32261
       have r₂ := eq87
       grind)
    | exact resolve eq32261 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32261
  have eq32286 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq32267
       grind)
    | exact superpose eq32267 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq32267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32267
  have eq32287 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32286
  have eq32292 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32287
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32287
    | exact resolve eq32287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32287
  have eq32293 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq32292
  have eq32310 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq32293
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32293
    | exact resolve eq32293 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32293
  have eq32651 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq32310 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq32310
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq32310
       grind)
    | exact resolve eq13 eq32310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32310
  have eq59442 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq32651
    | (have j0 := eq32651 (σ x)
       grind)
    | (have r₁ := eq32651 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq32651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32651
  have eq59452 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq59442
  have eq59474 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq59452 eq113
    | exact resolve eq113 eq59452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq59452
  have eq59509 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq59474
  have eq59538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq59509 eq24201
    | exact resolve eq24201 eq59509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24201 eq59509
  have eq59610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq59538
  have eq59616 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq59610
       have r₂ := eq27
       grind)
    | exact resolve eq59610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59610
  have eq59932 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq59616
       grind)
    | exact superpose eq59616 eq102
    | exact resolve eq102 eq59616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59947 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq59616
       grind)
    | exact superpose eq59616 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq59616
       grind)
    | exact resolve eq13 eq59616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59616
  have eq59976 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq59932
    | exact resolve eq59932 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59932
  have eq76145 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq59947 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59947
    | (have j0 := eq59947 x
       grind)
    | (have r₁ := eq59947 x
       have r₂ := eq18
       grind)
    | exact resolve eq59947 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59947
  have eq76154 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76145
  have eq76481 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq76154
       grind)
    | exact superpose eq76154 eq95
    | exact resolve eq95 eq76154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76504 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq828 x y
       have i₂ := eq76154
       grind)
    | exact superpose eq76154 eq828
    | (have j0 := eq828 x y
       grind)
    | exact resolve eq828 eq76154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76154
  have eq76507 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq76504
  have eq76511 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76507
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq76507
    | exact resolve eq76507 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76507
  have eq76526 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76481
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq76481
    | exact resolve eq76481 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76481
  have eq76530 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76511
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76511
    | exact resolve eq76511 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76511
  have eq76535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76530
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76530
    | exact resolve eq76530 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76530
  have eq76539 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq76535
    | exact resolve eq76535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76535
  have eq76543 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76539
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq76539
    | exact resolve eq76539 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76539
  have eq76547 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76543
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76543
    | exact resolve eq76543 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76543
  have eq76551 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq76547
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76547
    | exact resolve eq76547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76547
  have eq76555 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq76551
    | exact resolve eq76551 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76551
  have eq76646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76555 eq59976
    | exact resolve eq59976 eq76555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76555
  have eq76702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq76646
  have eq76716 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq76702
       have r₂ := eq27
       grind)
    | exact resolve eq76702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76702
  have eq77038 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq76716 eq88
    | (have r₁ := eq88
       have r₂ := eq76716
       grind)
    | exact resolve eq88 eq76716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq77077 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq77038
  have eq96398 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq77077 eq76526
    | exact resolve eq76526 eq77077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76526 eq77077
  have eq96406 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq96398
  have eq96570 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq96406
  have eq96653 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq96570
       have r₂ := eq76716
       grind)
    | exact resolve eq96570 eq76716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76716 eq96570
  have eq96691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq96653 eq59976
    | exact resolve eq59976 eq96653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59976 eq96653
  have eq96751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq96691
  have eq96767 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq96751
       have r₂ := eq27
       grind)
    | exact resolve eq96751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96751
  have eq97618 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq96767
       grind)
    | exact superpose eq96767 eq69
    | exact resolve eq69 eq96767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97619 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq96767
       grind)
    | exact superpose eq96767 eq87
    | (have r₁ := eq87
       have r₂ := eq96767
       grind)
    | exact resolve eq87 eq96767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq97648 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq97619
  have eq97665 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq97618
    | exact resolve eq97618 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97618
  have eq102358 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq97648
       grind)
    | exact superpose eq97648 eq95
    | exact resolve eq95 eq97648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102382 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq829 x y
       have i₂ := eq97648
       grind)
    | exact superpose eq97648 eq829
    | (have j0 := eq829 x y
       grind)
    | exact resolve eq829 eq97648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq97648
  have eq102386 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq102382
  have eq102393 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102386
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq102386
    | exact resolve eq102386 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102386
  have eq102409 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102358
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq102358
    | exact resolve eq102358 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102358
  have eq102414 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq97665 eq102393
    | exact resolve eq102393 eq97665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102393
  have eq102419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102414
    | exact resolve eq102414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102414
  have eq102423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102419
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102419
    | exact resolve eq102419 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102419
  have eq102427 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq102423
    | exact resolve eq102423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102423
  have eq102431 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq102427
       have r₂ := eq27
       grind)
    | exact resolve eq102427 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102427
  have eq102435 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102431
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq102431
    | exact resolve eq102431 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102431
  have eq102439 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102435
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102435
    | exact resolve eq102435 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102435
  have eq102443 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq102439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102439
    | exact resolve eq102439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102439
  have eq102447 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq102443
    | exact resolve eq102443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102443
  have eq103458 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq102447 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq102447
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq102447
       grind)
    | exact resolve eq13 eq102447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139773 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq103458
    | (have j0 := eq103458 (σ x)
       grind)
    | (have r₁ := eq103458 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq103458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103458
  have eq139792 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq139773
  have eq139807 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq97665 eq139792
    | exact resolve eq139792 eq97665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139792
  have eq139862 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq139807 eq102409
    | exact resolve eq102409 eq139807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102409 eq139807
  have eq139868 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq139862
  have eq140022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq139868 eq102447
    | exact resolve eq102447 eq139868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102447 eq139868
  have eq140092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq140022
  have eq140173 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq140092
       have r₂ := eq27
       grind)
    | exact resolve eq140092 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140092
  have eq140243 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq140173
       grind)
    | exact superpose eq140173 eq102
    | exact resolve eq102 eq140173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140268 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq140173
       grind)
    | exact superpose eq140173 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq140173
       grind)
    | exact resolve eq13 eq140173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140173
  have eq140303 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq140243
    | exact resolve eq140243 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140243
  have eq140633 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq140268 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq140268
    | (have j0 := eq140268 x
       grind)
    | (have r₁ := eq140268 x
       have r₂ := eq18
       grind)
    | exact resolve eq140268 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq140268
  have eq140642 : (M.op x x) = (k y x) := by grind
  clear eq140633
  have eq140644 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq140642
       have i₂ := eq96767
       grind)
    | exact superpose eq96767 eq140642
    | exact resolve eq140642 eq96767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96767 eq140642
  have eq140695 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq828 x y
       have i₂ := eq140644
       grind)
    | exact superpose eq140644 eq828
    | (have j0 := eq828 x y
       grind)
    | exact resolve eq828 eq140644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq140644
  have eq140705 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq140695
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq140695
    | exact resolve eq140695 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140695
  have eq140723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq97665 eq140705
    | (have r₁ := eq140705
       have r₂ := eq97665
       grind)
    | exact resolve eq140705 eq97665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140705
  have eq140729 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq140723
       have r₂ := eq20
       grind)
    | exact resolve eq140723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq140723
  have eq140733 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq140729
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq140729
    | exact resolve eq140729 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq140729
  have eq140737 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq97665 eq140733
    | exact resolve eq140733 eq97665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97665 eq140733
  have eq140741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq140737
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140737
    | exact resolve eq140737 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140737
  have eq140745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq140741
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140741
    | exact resolve eq140741 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140741
  have eq140749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq140745
    | exact resolve eq140745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140745
  have eq140753 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq140749
       have r₂ := eq27
       grind)
    | exact resolve eq140749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140749
  have eq140757 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq140753
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq140753
    | exact resolve eq140753 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq140753
  have eq140761 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq140303 eq140757
    | exact resolve eq140757 eq140303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140303 eq140757
  have eq140765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140761
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq140761
    | exact resolve eq140761 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq140761
  have eq140769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140765
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140765
    | exact resolve eq140765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq140765
  have eq140773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq140769
    | exact resolve eq140769 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq140769
  have eq140777 : False := by grind
  exact eq140777
