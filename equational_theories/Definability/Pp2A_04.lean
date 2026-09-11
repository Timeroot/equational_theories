import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_pxy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
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
  have eq52 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
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
  have eq67 : y ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq80 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
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
  have eq81 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
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
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq85
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
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
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq103
  have eq211 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq224 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq239 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op y X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq211 eq54
    | exact resolve eq54 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq249 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq215 eq54
    | exact resolve eq54 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq256 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq224 eq54
    | exact resolve eq54 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq296 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y X0 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) X0 (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq316 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq230 eq54
    | exact resolve eq54 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq565 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op x y))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq54
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq54 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq79
  have eq6689 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq6714 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq6689
    | exact resolve eq6689 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq6717 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq6714
       have r₂ := eq13 x x
       grind)
    | exact resolve eq6714 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714
  have eq6808 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80
    | (have j0 := eq80 x
       grind)
    | exact resolve eq80 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq6833 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6808
  have eq6842 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6833
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6833
    | exact resolve eq6833 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6833
  have eq6861 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6842
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6842 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842
  have eq6865 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6861 eq50
    | exact resolve eq50 eq6861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq6861
  have eq6881 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq6865
       have i₂ := eq6717
       grind)
    | exact superpose eq6717 eq6865
    | exact resolve eq6865 eq6717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6717 eq6865
  have eq6884 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq6881 eq15
    | exact resolve eq15 eq6881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6988 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq81 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq81
    | (have j0 := eq81 y
       grind)
    | exact resolve eq81 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq7011 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6988
  have eq7017 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7011
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq7011
    | exact resolve eq7011 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7011
  have eq7038 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq7017
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq7017 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq7065 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq7038 eq108
    | exact resolve eq108 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq9157 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7038 eq109
    | exact resolve eq109 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq20659 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq9157
       grind)
    | exact superpose eq9157 eq16
    | exact resolve eq16 eq9157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9157
  have eq20729 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7065 eq20659
    | exact resolve eq20659 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20659
  have eq20743 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq20729
       have r₂ := eq13 y y
       grind)
    | exact resolve eq20729 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq20744 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq20743
       grind)
    | exact superpose eq20743 eq77
    | exact resolve eq77 eq20743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq20777 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq7038 eq20744
    | exact resolve eq20744 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7038 eq20744
  have eq27859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq27860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq27859
    | exact resolve eq27859 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27859
  have eq27871 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq27860
       have r₂ := eq28
       grind)
    | exact resolve eq27860 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27860
  have eq27875 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27871 eq7065
    | exact resolve eq7065 eq27871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7065 eq27871
  have eq27939 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq27875
       have i₂ := eq20743
       grind)
    | exact superpose eq20743 eq27875
    | exact resolve eq27875 eq20743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20743 eq27875
  have eq27949 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq27939
    | exact resolve eq27939 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27939
  have eq27950 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq27949
  have eq27956 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27950 eq256
    | exact resolve eq256 eq27950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq27958 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27950 eq299
    | exact resolve eq299 eq27950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27950
  have eq27996 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq316 eq27956
    | exact resolve eq27956 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27956
  have eq28957 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27996 eq27958
    | exact resolve eq27958 eq27996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27958 eq27996
  have eq28995 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq28957
  have eq29010 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20777
       have i₂ := eq28995
       grind)
    | exact superpose eq28995 eq20777
    | exact resolve eq20777 eq28995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20777
  have eq29018 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq303 y
       have i₂ := eq28995
       grind)
    | exact superpose eq28995 eq303
    | exact resolve eq303 eq28995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28995
  have eq29054 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29018
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29018
    | exact resolve eq29018 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29018
  have eq29060 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29010
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29010
    | exact resolve eq29010 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29010
  have eq29068 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29054
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29054
    | exact resolve eq29054 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29054
  have eq29595 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29060 eq303
    | exact resolve eq303 eq29060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq29060
  have eq29632 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq29595
    | exact resolve eq29595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29595
  have eq29645 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq29632
    | exact resolve eq29632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29632
  have eq29646 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq29645
  have eq30191 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29646 eq61
    | exact resolve eq61 eq29646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29646
  have eq32820 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq30191
       have i₂ := eq29068
       grind)
    | exact superpose eq29068 eq30191
    | exact resolve eq30191 eq29068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29068 eq30191
  have eq32827 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq32820
  have eq32870 : (M.op x y) = (M.op x (M.op x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq239 x
       have i₂ := eq32827
       grind)
    | exact superpose eq32827 eq239
    | exact resolve eq239 eq32827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq32872 : y = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq296 y
       have i₂ := eq32827
       grind)
    | exact superpose eq32827 eq296
    | exact resolve eq296 eq32827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq32827
  have eq32913 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq249 eq32870
    | exact resolve eq32870 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq32870
  have eq33493 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32913 eq32872
    | exact resolve eq32872 eq32913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32872 eq32913
  have eq33536 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq33493
  have eq33631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33536 eq15
    | exact resolve eq15 eq33536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33536
  have eq33688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq33631
    | exact resolve eq33631 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33631
  have eq33690 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33688
       have r₂ := eq28
       grind)
    | exact resolve eq33688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33688
  have eq33695 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33690 eq68
    | (have r₁ := eq68
       have r₂ := eq33690
       grind)
    | exact resolve eq68 eq33690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq33690
  have eq33719 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq33695
  have eq34674 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33719 eq61
    | exact resolve eq61 eq33719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq33719
  have eq34698 : (k x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6881 eq34674
    | exact resolve eq34674 eq6881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34674
  have eq34702 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq34698
       have r₂ := eq67
       grind)
    | exact resolve eq34698 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq34698
  have eq34706 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq34702
       grind)
    | exact superpose eq34702 eq45
    | exact resolve eq45 eq34702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq34719 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq565 x y
       have i₂ := eq34702
       grind)
    | exact superpose eq34702 eq565
    | (have j0 := eq565 x y
       grind)
    | exact resolve eq565 eq34702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq34722 : (M.op x x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq34702
       grind)
    | exact superpose eq34702 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq34702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34723 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34722
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34722
    | exact resolve eq34722 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34722
  have eq34726 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34719
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34719
    | exact resolve eq34719 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34719
  have eq34737 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq34706
       have i₂ := eq6884
       grind)
    | exact superpose eq6884 eq34706
    | exact resolve eq34706 eq6884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34706
  have eq34741 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq316 eq34726
    | exact resolve eq34726 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq34726
  have eq34746 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34741
       have i₂ := eq6884
       grind)
    | exact superpose eq6884 eq34741
    | exact resolve eq34741 eq6884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884 eq34741
  have eq34751 : (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq299 eq34746
    | exact resolve eq34746 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq34746
  have eq34756 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34751
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34751
    | exact resolve eq34751 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34751
  have eq34761 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34756
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34756
    | exact resolve eq34756 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34756
  have eq34766 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34761
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34761
    | exact resolve eq34761 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34761
  have eq34771 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34766
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34766
    | exact resolve eq34766 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34766
  have eq34774 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34771
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34771
    | exact resolve eq34771 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34771
  have eq34777 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq34774
    | exact resolve eq34774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34774
  have eq42424 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  have eq42471 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34737 eq42424
    | exact resolve eq42424 eq34737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34737 eq42424
  have eq42483 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq42471
    | exact resolve eq42471 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42471
  have eq42487 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq42483
    | exact resolve eq42483 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42483
  have eq42488 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq42487
  have eq43816 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq42488 eq34777
    | exact resolve eq34777 eq42488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34777 eq42488
  have eq43857 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq43816
  have eq43869 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43857 eq28
    | exact resolve eq28 eq43857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43857
  have eq79997 : ∀ X0 : G, y = (M.op (M.op x x) (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y x
       have i₂ := eq34723
       grind)
    | exact superpose eq34723 eq56
    | exact resolve eq56 eq34723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34723
  have eq80034 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79997 x
       have i₂ := eq56 x x x
       grind)
    | exact superpose eq56 eq79997
    | exact resolve eq79997 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq79997
  have eq80065 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  have eq80109 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80065
       have i₂ := eq34702
       grind)
    | exact superpose eq34702 eq80065
    | exact resolve eq80065 eq34702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34702 eq80065
  have eq80125 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80109
    | exact resolve eq80109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80109
  have eq80130 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80125
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80125
    | exact resolve eq80125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80125
  have eq80131 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq80130
  have eq81190 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80034
       have i₂ := eq80131
       grind)
    | exact superpose eq80131 eq80034
    | exact resolve eq80034 eq80131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80034 eq80131
  have eq81229 : y = (M.op x y) ∨ x = y := by grind
  clear eq81190
  have eq81259 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq81229 eq21
    | exact resolve eq21 eq81229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81611 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81259
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq81259
    | exact resolve eq81259 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81259
  have eq82497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq81611 eq43869
    | (have r₁ := eq43869
       have r₂ := eq81611
       grind)
    | exact resolve eq43869 eq81611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43869 eq81611
  have eq82537 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq82497
  have eq82707 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq82537 eq29
    | exact resolve eq29 eq82537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq82537
  have eq82976 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq82707
    | exact resolve eq82707 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq82707
  have eq83960 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq82976 eq81229
    | exact resolve eq81229 eq82976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81229 eq82976
  have eq83961 : x = y := by grind
  clear eq83960
  have eq84192 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq83961
       grind)
    | exact superpose eq83961 eq19
    | exact resolve eq19 eq83961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq84193 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq83961
       grind)
    | exact superpose eq83961 eq25
    | exact resolve eq25 eq83961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq83961
  have eq84533 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq84193
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq84193
    | exact resolve eq84193 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq84193
  have eq85386 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq84533 eq27
    | exact resolve eq27 eq84533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq84533
  have eq86989 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq85386 eq6881
    | exact resolve eq6881 eq85386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6881 eq85386
  have eq87053 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq86989
       have i₂ := eq84192
       grind)
    | exact superpose eq84192 eq86989
    | exact resolve eq86989 eq84192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84192 eq86989
  have eq87070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87053 eq15
    | exact resolve eq15 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87053
  have eq87320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq87070
    | exact resolve eq87070 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq87070
  have eq87404 : False := by grind
  exact eq87404

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pyy_x_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq32 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq55 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y X0 x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) X0 (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq82 : ∀ X1 : G, (M.op x y) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq111
    | exact resolve eq111 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq111
  have eq173 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq112 (M.op X0 (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq112
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq328 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq82 eq54
    | exact resolve eq54 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq334 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq89 eq54
    | exact resolve eq54 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq399 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq67
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq400 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq399
    | exact resolve eq399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq404 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq400
    | exact resolve eq400 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq6906 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq328 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq328 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq328 eq9
    | exact resolve eq9 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6922 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq53 sF0
       have i₂ := eq328 sF0 x sF0
       grind)
    | (have i₁ := eq53 X0
       have i₂ := eq328 X0 x sF0
       grind)
    | exact superpose eq328 eq53
    | exact resolve eq53 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6927 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq89 sF2
       have i₂ := eq328 sF2 sF4 sF2
       grind)
    | (have i₁ := eq89 X0
       have i₂ := eq328 X0 sF4 sF2
       grind)
    | exact superpose eq328 eq89
    | exact resolve eq89 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq6933 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq59 sF4
       have i₂ := eq328 sF4 sF2 sF4
       grind)
    | (have i₁ := eq59 X0
       have i₂ := eq328 X0 sF2 sF4
       grind)
    | exact superpose eq328 eq59
    | exact resolve eq59 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq9301 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq6906 X0 x X1
       grind)
    | exact superpose eq6906 eq9
    | exact resolve eq9 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq42820 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9301 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))) x
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq9301
    | exact resolve eq9301 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq42975 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq42820 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42820
    | (have j0 := eq42820 x X0
       grind)
    | exact resolve eq42820 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42820
  have eq43305 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x (M.op x x)))) := by
    first
    | exact superpose eq6927 eq42975
    | (have j0 := eq42975 (σ y)
       grind)
    | exact resolve eq42975 eq6927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42975
  have eq44566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq404
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq404
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq404 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq44609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44566
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44566
    | exact resolve eq44566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44566
  have eq44612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq44609
    | exact resolve eq44609 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44609
  have eq44613 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq44612
       have r₂ := eq28
       grind)
    | exact resolve eq44612 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44612
  have eq44614 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq44613
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44613
    | exact resolve eq44613 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44613
  have eq44615 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44614 eq58
    | exact resolve eq58 eq44614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq44633 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44614 eq6933
    | exact resolve eq6933 eq44614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933 eq44614
  have eq44688 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq334 eq44633
    | exact resolve eq44633 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq44633
  have eq46003 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44688 eq44615
    | exact resolve eq44615 eq44688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44615 eq44688
  have eq46061 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq46003
  have eq46113 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq46061 eq220
    | exact resolve eq220 eq46061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq46061
  have eq46168 : (τ (σ y)) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39 eq46113
    | exact resolve eq46113 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46113
  have eq46191 : y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq46168
    | exact resolve eq46168 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46168
  have eq46192 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq46191
  have eq46196 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq46192
       grind)
    | exact superpose eq46192 eq55
    | exact resolve eq55 eq46192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq46213 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6922 y
       have i₂ := eq46192
       grind)
    | exact superpose eq46192 eq6922
    | exact resolve eq6922 eq46192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922 eq46192
  have eq46267 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq332 eq46213
    | exact resolve eq46213 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq46213
  have eq47041 : x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq46267 eq46196
    | exact resolve eq46196 eq46267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46196 eq46267
  have eq47101 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq47041
  have eq48461 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43305
       have i₂ := eq47101
       grind)
    | exact superpose eq47101 eq43305
    | exact resolve eq43305 eq47101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43305
  have eq48488 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq47101
       grind)
    | exact superpose eq47101 eq112
    | exact resolve eq112 eq47101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48489 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq173 x
       have i₂ := eq47101
       grind)
    | exact superpose eq47101 eq173
    | exact resolve eq173 eq47101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq47101
  have eq48546 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48489
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48489
    | exact resolve eq48489 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48489
  have eq48547 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48488
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48488
    | exact resolve eq48488 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48488
  have eq48557 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48461
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48461
    | exact resolve eq48461 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48461
  have eq48563 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48546
    | exact resolve eq48546 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48546
  have eq48564 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48547
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq48547
    | exact resolve eq48547 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48547
  have eq48568 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48557
    | exact resolve eq48557 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48557
  have eq48571 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48563
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48563
    | exact resolve eq48563 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48563
  have eq48684 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48564 eq59
    | exact resolve eq59 eq48564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq48564
  have eq48773 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48684
    | exact resolve eq48684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48684
  have eq48800 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq48568 eq9
    | exact resolve eq9 eq48568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48568
  have eq48921 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48773 eq6927
    | exact resolve eq6927 eq48773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927 eq48773
  have eq58453 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48571 eq48800
    | exact resolve eq48800 eq48571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48571 eq48800
  have eq58635 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58453
  have eq58646 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq335 eq58635
    | exact resolve eq58635 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq58635
  have eq58652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq58646 eq48921
    | exact resolve eq48921 eq58646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48921 eq58646
  have eq58720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58652
  have eq58734 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq58720
       have r₂ := eq28
       grind)
    | exact resolve eq58720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58720
  have eq58741 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq58734 eq40
    | exact resolve eq40 eq58734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq58734
  have eq58807 : x = y ∨ x = y := by
    first
    | exact superpose eq39 eq58741
    | exact resolve eq58741 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq58741
  have eq58808 : x = y := by grind
  clear eq58807
  have eq58812 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq58808
       grind)
    | exact superpose eq58808 eq19
    | exact resolve eq19 eq58808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq58813 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq58808
       grind)
    | exact superpose eq58808 eq25
    | exact resolve eq25 eq58808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq58808
  have eq61803 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq58813
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq58813
    | exact resolve eq58813 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58813
  have eq62665 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq61803 eq27
    | exact resolve eq27 eq61803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq61803
  have eq65601 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq58812
       grind)
    | exact superpose eq58812 eq112
    | exact resolve eq112 eq58812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq58812
  have eq66013 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65601
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65601
    | exact resolve eq65601 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq65601
  have eq66371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62665 eq66013
    | exact resolve eq66013 eq62665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62665 eq66013
  have eq66599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq66371
    | exact resolve eq66371 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq66371
  have eq66761 : False := by grind
  exact eq66761

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_pyx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq79 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq96 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
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
  have eq97 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
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
  clear eq24
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq80 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq220 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq143 X0 X1
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq143
    | (have j0 := eq143 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq143 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq143 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq143 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq223 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq220 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq225 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq223 (M.op X1 (k X1 X1)) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq223 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq223 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq227 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq222 X1
       grind)
    | exact superpose eq222 eq225
    | (have j0 := eq225 X0 X1
       grind)
    | exact resolve eq225 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq232 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq222 (σ X0)
       grind)
    | exact superpose eq222 eq15
    | exact resolve eq15 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq232 X0
       have i₂ := eq222 X0
       grind)
    | exact superpose eq222 eq232
    | exact resolve eq232 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq232
  have eq369 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq9
    | exact resolve eq9 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq10
    | (have j1 := eq47 X0 X1
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq908 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq786
    | (have j0 := eq786 X0 X1
       grind)
    | exact resolve eq786 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq982 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq908 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq908
    | (have j0 := eq908 X0 X1
       grind)
    | exact resolve eq908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1373 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq97 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq97 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1878 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq1373 X0 x X1
       grind)
    | exact superpose eq1373 eq9
    | exact resolve eq9 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq2041 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1878 (σ X0) (σ X0) x
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq1878
    | exact resolve eq1878 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq2647 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2041 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq2041
    | exact resolve eq2041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq3021 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq369 (M.op X0 (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq2647 X0 X1
       grind)
    | exact superpose eq2647 eq369
    | exact resolve eq369 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq2647
  have eq3058 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3021 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq3021
    | exact resolve eq3021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3074 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3058 X0 x
       have i₂ := eq96 (σ X0) (σ X0) x
       grind)
    | exact superpose eq96 eq3058
    | exact resolve eq3058 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq3058
  have eq3078 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3074 X0
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq3074
    | exact resolve eq3074 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq3074
  have eq10043 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq982 X0 X1
       grind)
    | exact superpose eq982 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq982 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq982 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq982 X0 (M.op X1 (M.op X0 X0))
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq982 X0 X1
       grind)
    | exact resolve eq12 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq10100 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10043
  have eq10126 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10100 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10100
    | (have j0 := eq10100 X0 X1
       grind)
    | exact resolve eq10100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10100
  have eq10127 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10126
  have eq10376 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10127 x y
       grind)
    | exact superpose eq10127 eq16
    | (have j1 := eq10127 x y
       grind)
    | exact resolve eq16 eq10127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10127
  have eq11164 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10376
       have i₂ := eq227 y x
       grind)
    | exact superpose eq227 eq10376
    | (have j1 := eq227 y x
       grind)
    | exact resolve eq10376 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq10376
  have eq11165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq11164
  have eq11166 : y = (M.op x x) := by grind
  clear eq11165
  have eq11276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3078 x
       have i₂ := eq11166
       grind)
    | exact superpose eq11166 eq3078
    | exact resolve eq3078 eq11166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078 eq11166
  have eq11353 : False := by grind
  exact eq11353

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X2 (M.op X2 X0)) (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 (M.op X2 X0)) (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) ≠ X0 ∨ (k (M.op X0 (M.op X0 X0)) X1) = X0 ∨ (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq13 eq9
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
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq105 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq132 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
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
  have eq133 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
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
  have eq146 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 (M.op X0 X0)) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq56
    | (have j0 := eq56 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq56 X0 (M.op X0 X1)
       have r₂ := eq9 X0 X1 X0
       grind)
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq459 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq453 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq463 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq459 X0 X1
       have j1 := eq34 X0 X1 X0
       grind)
    | (have r₁ := eq459 X0 X1
       have r₂ := eq34 X0 X1 x
       grind)
    | exact resolve eq459 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq459
  have eq544 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq577 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq544
  have eq582 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq577 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq577 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq577 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq586 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq582
    | (have j0 := eq582 X0 X1
       grind)
    | exact resolve eq582 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq582
  have eq627 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X2 X0
       have i₂ := eq133 X1 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1 X0
       have i₂ := eq133 X0 X1 X0
       grind)
    | exact superpose eq133 eq19
    | exact resolve eq19 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq667 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq133 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq133 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq133 eq9
    | exact resolve eq9 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq853 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq463 (M.op X0 X0) X1
       have i₂ := eq667 X0 X0 X0
       grind)
    | exact superpose eq667 eq463
    | exact resolve eq463 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq856 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X0)) = (M.op (M.op X0 X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq627 X3 (M.op X0 X1) (M.op X2 X0)
       have i₂ := eq667 X0 X1 X2
       grind)
    | exact superpose eq667 eq627
    | exact resolve eq627 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq860 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq667 X0 x X1
       grind)
    | exact superpose eq667 eq9
    | exact resolve eq9 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq860 (τ X0) (τ X0) x
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq860
    | exact resolve eq860 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq586 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq586
    | exact resolve eq586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq586 (σ X1) X0
       grind)
    | exact superpose eq586 eq15
    | (have j1 := eq586 (σ X1) X0
       grind)
    | exact resolve eq15 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq1246 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1233 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq1233
    | (have j0 := eq1233 X0 X1
       grind)
    | exact resolve eq1233 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1994 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1219 (τ X0) X1
       grind)
    | exact superpose eq1219 eq18
    | (have j1 := eq1219 (τ X0) X1
       grind)
    | exact resolve eq18 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1219
  have eq3048 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq991 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq991
    | exact resolve eq991 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq3272 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq146 (M.op X0 (M.op X0 X0)) (M.op (τ X0) X1)
       have i₂ := eq3048 X0 X1
       grind)
    | exact superpose eq3048 eq146
    | exact resolve eq146 eq3048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq3048
  have eq3313 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (M.op (τ X0) X1) (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3272 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq3272
    | exact resolve eq3272 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq3325 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3313 X0 x
       have i₂ := eq132 (τ X0) (τ X0) x
       grind)
    | exact superpose eq132 eq3313
    | exact resolve eq3313 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq3313
  have eq3329 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3325 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq3325
    | exact resolve eq3325 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq3325
  have eq12174 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0)))) = (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3329 (M.op x x)
       have i₂ := eq856 x x x x
       grind)
    | (have i₁ := eq3329 (M.op x x)
       have i₂ := eq856 x x x x
       grind)
    | exact superpose eq856 eq3329
    | exact resolve eq3329 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq3329
  have eq12238 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12174 X0 X1
       have i₂ := eq667 X0 X0 X1
       grind)
    | exact superpose eq667 eq12174
    | exact resolve eq12174 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq12174
  have eq34887 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ X0) X2) (τ (M.op (M.op X0 X0) (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq860 (τ (M.op (M.op X0 X0) (M.op X1 X0))) (τ (M.op X0 X0)) X2
       have i₂ := eq12238 X0 X1
       grind)
    | exact superpose eq12238 eq860
    | exact resolve eq860 eq12238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq12238
  have eq38363 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op (M.op (τ (σ X0)) X1) (τ (M.op (σ (M.op X0 X0)) (M.op X2 (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34887 (σ X0) X2 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq34887
    | exact resolve eq34887 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq34887
  have eq38715 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (τ (M.op (σ (M.op X0 X0)) (M.op X2 (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38363 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38363
    | exact resolve eq38363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38363
  have eq60873 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1246 x y
       grind)
    | exact superpose eq1246 eq16
    | (have j1 := eq1246 x y
       grind)
    | exact resolve eq16 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq301200 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1994 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1994
    | exact resolve eq1994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq301824 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq301200 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq301200
    | (have j0 := eq301200 X0 X1
       grind)
    | exact resolve eq301200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301200
  have eq518692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq60873
       have i₂ := eq301824 x y
       grind)
    | exact superpose eq301824 eq60873
    | (have j1 := eq301824 x y
       grind)
    | (have r₁ := eq60873
       have r₂ := eq301824 x y
       grind)
    | exact resolve eq60873 eq301824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518695 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq518692
  have eq519148 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq518695
       grind)
    | exact superpose eq518695 eq16
    | exact resolve eq16 eq518695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519216 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq84 y (σ x)
       have i₂ := eq518695
       grind)
    | exact superpose eq518695 eq84
    | (have j0 := eq84 y (σ x)
       grind)
    | (have r₁ := eq84 y (σ x)
       have r₂ := eq518695
       grind)
    | exact resolve eq84 eq518695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq519243 : (σ x) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq518695
       grind)
    | exact superpose eq518695 eq12
    | exact resolve eq12 eq518695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518695
  have eq519540 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq519216
  have eq519700 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq519243
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq519243
    | exact resolve eq519243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519243
  have eq519708 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq519540
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq519540
    | exact resolve eq519540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519540
  have eq519853 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq519708
       have r₂ := eq519700
       grind)
    | exact resolve eq519708 eq519700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519700 eq519708
  have eq520256 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq301824 x y
       have i₂ := eq519853
       grind)
    | exact superpose eq519853 eq301824
    | (have j0 := eq301824 x y
       grind)
    | exact resolve eq301824 eq519853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301824 eq519853
  have eq520495 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq520256
  have eq520531 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq520495
       have r₂ := eq519148
       grind)
    | exact resolve eq520495 eq519148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519148 eq520495
  have eq520588 : ∀ X0 : G, (M.op x y) = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq853 y x
       have i₂ := eq520531
       grind)
    | exact superpose eq520531 eq853
    | exact resolve eq853 eq520531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq522227 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq520588 (τ (M.op (σ (M.op x x)) (M.op x (σ x))))
       have i₂ := eq38715 x y x
       grind)
    | exact superpose eq38715 eq520588
    | exact resolve eq520588 eq38715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38715 eq520588
  have eq523174 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq60873
       have i₂ := eq522227
       grind)
    | exact superpose eq522227 eq60873
    | exact resolve eq60873 eq522227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60873 eq522227
  have eq523191 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq523174
  have eq523201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq523191
       have i₂ := eq520531
       grind)
    | exact superpose eq520531 eq523191
    | exact resolve eq523191 eq520531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520531 eq523191
  have eq523208 : False := by grind
  exact eq523208

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq257 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq264 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq257 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq257 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq257 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq257
  have eq2511 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq264
  have eq2551 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2511 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2638 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2551 (σ X1) (σ X0)
       grind)
    | exact superpose eq2551 eq15
    | exact resolve eq15 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2643 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2638 X0 X1
       have i₂ := eq2551 X1 X0
       grind)
    | exact superpose eq2551 eq2638
    | exact resolve eq2638 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq2638
  have eq2647 : False := by grind
  exact eq2647

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq55 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq55 X0 X1 X2
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq154 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq172 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq198 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq212 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq198 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq213 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq217 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq213
    | exact resolve eq213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq213
    | exact resolve eq213 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq219 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq218
    | exact resolve eq218 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq220 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq217
    | exact resolve eq217 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq217
  have eq228 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq9
    | exact resolve eq9 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (σ X0) X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq172
    | (have j0 := eq172 (σ X0) X1
       grind)
    | exact resolve eq172 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq64 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq726 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 (M.op X1 x)
       have i₂ := eq530 X1 x X0
       grind)
    | exact superpose eq530 eq9
    | exact resolve eq9 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq765 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq726 (σ X0) (σ X0) x
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq726
    | exact resolve eq726 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq978 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq765 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq765
    | exact resolve eq765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq1083 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (σ (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq978 (τ X0) X1
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq978
    | exact resolve eq978 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq978
  have eq1101 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op (τ X0) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1083
    | exact resolve eq1083 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1308 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (σ (M.op (M.op (τ X0) (τ (M.op X0 X0))) (M.op (τ X0) (τ (M.op X0 X0))))) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 (M.op (τ X0) (τ (M.op X0 X0))) (M.op X0 X1)
       have i₂ := eq1101 X0 X1
       grind)
    | exact superpose eq1101 eq248
    | exact resolve eq248 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1101
  have eq1324 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (σ (τ X0)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1308 X0 X1
       have i₂ := eq228 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq228 eq1308
    | exact resolve eq1308 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq1308
  have eq1339 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1324 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1324
    | exact resolve eq1324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1349 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1339 X0 x
       have i₂ := eq63 X0 X0 x
       grind)
    | exact superpose eq63 eq1339
    | exact resolve eq1339 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1339
  have eq1659 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq1349 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1349
    | exact resolve eq1349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1706 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1659 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq1659
    | exact resolve eq1659 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq1659
  have eq1713 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1706 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1706
    | exact resolve eq1706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq3667 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq255 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq255 X0 (σ X0)
       grind)
    | exact superpose eq255 eq10
    | (have j1 := eq255 X0 X1
       grind)
    | exact resolve eq10 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq4380 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3667 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3667
    | (have j0 := eq3667 X1 (σ X0)
       grind)
    | exact resolve eq3667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq4510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4380 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4380
    | (have j0 := eq4380 X0 X1
       grind)
    | exact resolve eq4380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4380
  have eq5138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4510 y x
       grind)
    | exact superpose eq4510 eq16
    | (have j1 := eq4510 y x
       grind)
    | exact resolve eq16 eq4510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq5264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5138
       have i₂ := eq172 x y
       grind)
    | exact superpose eq172 eq5138
    | (have j1 := eq172 x y
       grind)
    | exact resolve eq5138 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq5138
  have eq5271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq5264
  have eq5272 : y = (M.op x x) := by grind
  clear eq5271
  have eq5293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1713 x
       have i₂ := eq5272
       grind)
    | exact superpose eq5272 eq1713
    | exact resolve eq1713 eq5272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq5272
  have eq6547 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5293
       grind)
    | exact superpose eq5293 eq16
    | (have r₁ := eq16
       have r₂ := eq5293
       grind)
    | exact resolve eq16 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq6579 : False := by grind
  exact eq6579

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq55 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq55 X0 X1 X2
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq154 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq172 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq198 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq212 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq198 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq213 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq217 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq213
    | exact resolve eq213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq213
    | exact resolve eq213 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq219 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq218
    | exact resolve eq218 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq220 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq213 X0
       grind)
    | exact superpose eq213 eq217
    | exact resolve eq217 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq217
  have eq228 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq9
    | exact resolve eq9 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (σ X0) X1
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq172
    | (have j0 := eq172 (σ X0) X1
       grind)
    | exact resolve eq172 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq64 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq728 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 (M.op X1 x)
       have i₂ := eq530 X1 x X0
       grind)
    | exact superpose eq530 eq9
    | exact resolve eq9 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq767 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq728 (σ X0) (σ X0) x
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq728
    | exact resolve eq728 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq980 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq767 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq767
    | exact resolve eq767 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1085 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (σ (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq980 (τ X0) X1
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq980
    | exact resolve eq980 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq980
  have eq1103 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op (τ X0) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1085
    | exact resolve eq1085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1310 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (σ (M.op (M.op (τ X0) (τ (M.op X0 X0))) (M.op (τ X0) (τ (M.op X0 X0))))) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 (M.op (τ X0) (τ (M.op X0 X0))) (M.op X0 X1)
       have i₂ := eq1103 X0 X1
       grind)
    | exact superpose eq1103 eq248
    | exact resolve eq248 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1103
  have eq1326 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (M.op (σ (τ X0)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1310 X0 X1
       have i₂ := eq228 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq228 eq1310
    | exact resolve eq1310 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq1310
  have eq1341 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1326 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1326
    | exact resolve eq1326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1351 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1341 X0 x
       have i₂ := eq63 X0 X0 x
       grind)
    | exact superpose eq63 eq1341
    | exact resolve eq1341 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1341
  have eq1659 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq1351 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1351
    | exact resolve eq1351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1706 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq1659 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq1659
    | exact resolve eq1659 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq1659
  have eq1713 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1706 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1706
    | exact resolve eq1706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq3735 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq255 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq255 X0 (σ X0)
       grind)
    | exact superpose eq255 eq10
    | (have j1 := eq255 X0 X1
       grind)
    | exact resolve eq10 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq4185 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3735 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3735
    | (have j0 := eq3735 X1 (σ X0)
       grind)
    | exact resolve eq3735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735
  have eq4310 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4185 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4185
    | (have j0 := eq4185 X0 X1
       grind)
    | exact resolve eq4185 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq5382 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4310 y x
       grind)
    | exact superpose eq4310 eq16
    | (have j1 := eq4310 y x
       grind)
    | exact resolve eq16 eq4310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4310
  have eq5517 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5382
       have i₂ := eq172 x y
       grind)
    | exact superpose eq172 eq5382
    | (have j1 := eq172 x y
       grind)
    | exact resolve eq5382 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq5382
  have eq5522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq5517
  have eq5523 : y = (M.op x x) := by grind
  clear eq5522
  have eq5543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1713 x
       have i₂ := eq5523
       grind)
    | exact superpose eq5523 eq1713
    | exact resolve eq1713 eq5523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq5523
  have eq6918 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5543
       grind)
    | exact superpose eq5543 eq16
    | (have r₁ := eq16
       have r₂ := eq5543
       grind)
    | exact resolve eq16 eq5543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5543
  have eq6948 : False := by grind
  exact eq6948

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq166 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X0 X1
       have i₂ := eq98 X1
       grind)
    | exact superpose eq98 eq171
    | (have j0 := eq171 X0 X1
       grind)
    | exact resolve eq171 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq197 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq172 y x
       grind)
    | exact superpose eq172 eq16
    | (have j1 := eq172 y x
       grind)
    | exact resolve eq16 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq197
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq197
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq197 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq197
  have eq547 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq546
  have eq1512 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq109
    | exact resolve eq109 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq166
  have eq8851 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) (M.op (σ (M.op (τ X0) (τ X0))) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1512 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1512
    | exact resolve eq1512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq8965 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8851 X0 X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq8851
    | exact resolve eq8851 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq8851
  have eq9047 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8965 y y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq8965
    | exact resolve eq8965 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq9136 : x = y ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9047
       have i₂ := eq8965 x x
       grind)
    | exact superpose eq8965 eq9047
    | exact resolve eq9047 eq8965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9047
  have eq9534 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9136
       grind)
    | exact superpose eq9136 eq16
    | exact resolve eq16 eq9136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9136
  have eq9535 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9534
       have r₂ := eq98 x
       grind)
    | exact resolve eq9534 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9534
  have eq9800 : (M.op y y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq9535
       grind)
    | exact superpose eq9535 eq10
    | exact resolve eq10 eq9535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9535
  have eq9860 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9800
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq9800
    | exact resolve eq9800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9800
  have eq9939 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq8965 y y
       have i₂ := eq9860
       grind)
    | exact superpose eq9860 eq8965
    | exact resolve eq8965 eq9860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9860
  have eq9941 : x = y := by
    first
    | (have i₁ := eq9939
       have i₂ := eq8965 x x
       grind)
    | exact superpose eq8965 eq9939
    | exact resolve eq9939 eq8965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8965 eq9939
  have eq10078 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9941
       grind)
    | exact superpose eq9941 eq16
    | exact resolve eq16 eq9941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9941
  have eq10079 : False := by grind
  exact eq10079
