import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxx_pxy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq37
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq303 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
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
  have eq567 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op x y))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq6715 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq6740 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq6715
    | exact resolve eq6715 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715
  have eq6743 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq6740
       have r₂ := eq13 x x
       grind)
    | exact resolve eq6740 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6740
  have eq6744 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq6743
       grind)
    | exact superpose eq6743 eq44
    | exact resolve eq44 eq6743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7005 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq172
    | (have j0 := eq172 x
       grind)
    | exact resolve eq172 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq7030 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7005
  have eq7040 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7030
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq7030
    | exact resolve eq7030 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq7030
  have eq7061 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7040
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq7040 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7040
  have eq7065 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq7061 eq50
    | exact resolve eq50 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7081 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq7065
       have i₂ := eq6743
       grind)
    | exact superpose eq6743 eq7065
    | exact resolve eq7065 eq6743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743 eq7065
  have eq7249 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq194
    | (have j0 := eq194 y
       grind)
    | exact resolve eq194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq7276 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq7249
  have eq7283 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7276
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq7276
    | exact resolve eq7276 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq7309 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq7283
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq7283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7283
  have eq7348 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq7309 eq108
    | exact resolve eq108 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq9038 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7309 eq109
    | exact resolve eq109 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq21029 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq9038
       grind)
    | exact superpose eq9038 eq16
    | exact resolve eq16 eq9038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9038
  have eq21099 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7348 eq21029
    | exact resolve eq21029 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21029
  have eq21112 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21099
       have r₂ := eq13 y y
       grind)
    | exact resolve eq21099 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21099
  have eq21116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq21112
       grind)
    | exact superpose eq21112 eq77
    | exact resolve eq77 eq21112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq21149 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq7309 eq21116
    | exact resolve eq21116 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309 eq21116
  have eq28194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq28195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq28194
    | exact resolve eq28194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28194
  have eq28206 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq28195
       have r₂ := eq28
       grind)
    | exact resolve eq28195 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28195
  have eq28216 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28206 eq7081
    | exact resolve eq7081 eq28206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28206
  have eq28266 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq28216
    | exact resolve eq28216 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28216
  have eq28267 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq28266
  have eq28280 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28267 eq256
    | exact resolve eq256 eq28267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq28282 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28267 eq299
    | exact resolve eq299 eq28267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28267
  have eq28320 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq316 eq28280
    | exact resolve eq28280 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28280
  have eq29282 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28320 eq28282
    | exact resolve eq28282 eq28320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28282 eq28320
  have eq29320 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq29282
  have eq29329 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6744
       have i₂ := eq29320
       grind)
    | exact superpose eq29320 eq6744
    | exact resolve eq6744 eq29320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29340 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq303 x
       have i₂ := eq29320
       grind)
    | exact superpose eq29320 eq303
    | exact resolve eq303 eq29320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29320
  have eq29379 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29340
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29340
    | exact resolve eq29340 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29340
  have eq29388 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7061 eq29329
    | exact resolve eq29329 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29329
  have eq29390 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29379
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29379
    | exact resolve eq29379 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29379
  have eq29396 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29388
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29388
    | exact resolve eq29388 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29388
  have eq29957 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29396 eq303
    | exact resolve eq303 eq29396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq29998 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq29957
    | exact resolve eq29957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29957
  have eq30008 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq29998
    | exact resolve eq29998 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29998
  have eq30009 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq30008
  have eq30624 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30009 eq61
    | exact resolve eq61 eq30009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32868 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq30624
       have i₂ := eq29390
       grind)
    | exact superpose eq29390 eq30624
    | exact resolve eq30624 eq29390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29390 eq30624
  have eq32875 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq32868
  have eq32918 : (M.op x y) = (M.op x (M.op x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq239 x
       have i₂ := eq32875
       grind)
    | exact superpose eq32875 eq239
    | exact resolve eq239 eq32875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq32920 : y = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq296 y
       have i₂ := eq32875
       grind)
    | exact superpose eq32875 eq296
    | exact resolve eq296 eq32875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq32875
  have eq32960 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq249 eq32918
    | exact resolve eq32918 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq32918
  have eq33564 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32960 eq32920
    | exact resolve eq32920 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32920 eq32960
  have eq33609 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq33564
  have eq33617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33609 eq15
    | exact resolve eq15 eq33609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33609
  have eq33674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq33617
    | exact resolve eq33617 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33617
  have eq33675 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33674
       have r₂ := eq28
       grind)
    | exact resolve eq33674 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33674
  have eq33676 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33675 eq28
    | exact resolve eq28 eq33675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33679 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33675 eq68
    | (have r₁ := eq68
       have r₂ := eq33675
       grind)
    | exact resolve eq68 eq33675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq33681 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33675 eq230
    | exact resolve eq230 eq33675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq33675
  have eq33703 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq33679
  have eq35012 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33703 eq61
    | exact resolve eq61 eq33703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq33703
  have eq35036 : (k x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7081 eq35012
    | exact resolve eq35012 eq7081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35012
  have eq35040 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq35036
       have r₂ := eq67
       grind)
    | exact resolve eq35036 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq35036
  have eq35044 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq35040
       grind)
    | exact superpose eq35040 eq45
    | exact resolve eq45 eq35040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq35057 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq567 x y
       have i₂ := eq35040
       grind)
    | exact superpose eq35040 eq567
    | (have j0 := eq567 x y
       grind)
    | exact resolve eq567 eq35040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq35060 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq35040
       grind)
    | exact superpose eq35040 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq35040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35061 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35060
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35060
    | exact resolve eq35060 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35060
  have eq35064 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35057
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35057
    | exact resolve eq35057 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35057
  have eq35075 : (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35044
       have i₂ := eq6744
       grind)
    | exact superpose eq6744 eq35044
    | exact resolve eq35044 eq6744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35044
  have eq35079 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq316 eq35064
    | exact resolve eq35064 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq35064
  have eq35086 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7061 eq35075
    | exact resolve eq35075 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35075
  have eq35089 : (σ y) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35079
       have i₂ := eq6744
       grind)
    | exact superpose eq6744 eq35079
    | exact resolve eq35079 eq6744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35079
  have eq35094 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7061 eq35089
    | exact resolve eq35089 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35089
  have eq35099 : (σ y) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq299 eq35094
    | exact resolve eq35094 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq35094
  have eq35104 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35099
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35099
    | exact resolve eq35099 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35099
  have eq35109 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35104
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35104
    | exact resolve eq35104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35104
  have eq35114 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35109
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35109
    | exact resolve eq35109 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35109
  have eq35119 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35114
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35114
    | exact resolve eq35114 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35114
  have eq35122 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35119
    | exact resolve eq35119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35119
  have eq35125 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq35122
    | exact resolve eq35122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35122
  have eq35127 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30009 eq35086
    | exact resolve eq35086 eq30009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30009
  have eq42756 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35125 eq7348
    | exact resolve eq7348 eq35125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7348
  have eq42775 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq35125
  have eq42818 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35086 eq42775
    | exact resolve eq42775 eq35086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35086 eq42775
  have eq42830 : (τ (σ x)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42756
       have i₂ := eq21112
       grind)
    | exact superpose eq21112 eq42756
    | exact resolve eq42756 eq21112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21112 eq42756
  have eq42831 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq42818
    | exact resolve eq42818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42818
  have eq42840 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq42830
    | exact resolve eq42830 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42830
  have eq42841 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq42831
    | exact resolve eq42831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42831
  have eq42842 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq42841
  have eq44197 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq42842 eq7081
    | exact resolve eq7081 eq42842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42842
  have eq52308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq35127 eq29396
    | exact resolve eq29396 eq35127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29396 eq35127
  have eq52349 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52308
  have eq52765 : ∀ X0 : G, (M.op (M.op X0 y) x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56 x X0 y
       have i₂ := eq52349
       grind)
    | exact superpose eq52349 eq56
    | exact resolve eq56 eq52349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52349
  have eq54927 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52765 y
       have i₂ := eq42840
       grind)
    | exact superpose eq42840 eq52765
    | exact resolve eq52765 eq42840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42840 eq52765
  have eq54968 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq54927
  have eq60662 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44197
       have i₂ := eq54968
       grind)
    | exact superpose eq54968 eq44197
    | exact resolve eq44197 eq54968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44197 eq54968
  have eq60704 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq60662
  have eq60742 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq60704 eq15
    | exact resolve eq15 eq60704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60704
  have eq60865 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq60742
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60742
    | exact resolve eq60742 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60742
  have eq60866 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq60865
  have eq61258 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq60866 eq28
    | exact resolve eq28 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60866
  have eq93310 : ∀ X0 : G, y = (M.op (M.op x x) (M.op x X0)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y x
       have i₂ := eq35061
       grind)
    | exact superpose eq35061 eq56
    | exact resolve eq56 eq35061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35061
  have eq93347 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93310 x
       have i₂ := eq56 x x x
       grind)
    | exact superpose eq56 eq93310
    | exact resolve eq93310 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq93310
  have eq93366 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21149
       have i₂ := eq93347
       grind)
    | exact superpose eq93347 eq21149
    | exact resolve eq21149 eq93347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21149
  have eq93382 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq93347
  have eq93422 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93382
       have i₂ := eq35040
       grind)
    | exact superpose eq35040 eq93382
    | exact resolve eq93382 eq35040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35040 eq93382
  have eq93432 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93366
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq93366
    | exact resolve eq93366 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93366
  have eq93440 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93422
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93422
    | exact resolve eq93422 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93422
  have eq93444 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93440
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93440
    | exact resolve eq93440 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93440
  have eq93445 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq93444
  have eq95769 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93432 eq33681
    | exact resolve eq33681 eq93432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33681 eq93432
  have eq95807 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq95769
  have eq96543 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6744
       have i₂ := eq93445
       grind)
    | exact superpose eq93445 eq6744
    | exact resolve eq6744 eq93445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744 eq93445
  have eq96620 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7061 eq96543
    | exact resolve eq96543 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7061 eq96543
  have eq96627 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq96620
    | exact resolve eq96620 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96620
  have eq98317 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq96627 eq95807
    | exact resolve eq95807 eq96627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95807 eq96627
  have eq98360 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq98317
  have eq98372 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq98360
       have r₂ := eq33676
       grind)
    | exact resolve eq98360 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33676 eq98360
  have eq98386 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq98372 eq21
    | exact resolve eq21 eq98372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98742 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq98386
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq98386
    | exact resolve eq98386 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98386
  have eq99675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq98742 eq61258
    | (have r₁ := eq61258
       have r₂ := eq98742
       grind)
    | exact resolve eq61258 eq98742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61258 eq98742
  have eq99706 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq99675
  have eq99880 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq99706 eq29
    | exact resolve eq29 eq99706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq99706
  have eq100156 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq99880
    | exact resolve eq99880 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq99880
  have eq100451 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq100156 eq98372
    | exact resolve eq98372 eq100156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98372 eq100156
  have eq100452 : x = y := by grind
  clear eq100451
  have eq101401 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq100452
       grind)
    | exact superpose eq100452 eq19
    | exact resolve eq19 eq100452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq101402 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq100452
       grind)
    | exact superpose eq100452 eq25
    | exact resolve eq25 eq100452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq100452
  have eq101752 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq101402
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq101402
    | exact resolve eq101402 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq101402
  have eq101809 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq101752 eq27
    | exact resolve eq27 eq101752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq101752
  have eq104068 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101809 eq7081
    | exact resolve eq7081 eq101809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7081 eq101809
  have eq104128 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq104068
       have i₂ := eq101401
       grind)
    | exact superpose eq101401 eq104068
    | exact resolve eq104068 eq101401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101401 eq104068
  have eq104148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104128 eq15
    | exact resolve eq15 eq104128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104128
  have eq104426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq104148
    | exact resolve eq104148 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq104148
  have eq104518 : False := by grind
  exact eq104518

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pxx_pyy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X2 (M.op x x)
       have i₂ := eq14 X0 X2 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq79 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq101 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq101
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
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
  have eq151 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq134
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq151
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq194 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq209 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq249 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq215 eq54
    | exact resolve eq54 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq56 X2 X0 X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq215 eq56
    | exact resolve eq56 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq211 eq56
    | exact resolve eq56 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq56
    | exact resolve eq56 eq224
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
  have eq318 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq230 eq56
    | exact resolve eq56 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq338 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X1 X2)) X1
       have r₂ := eq57 X1 X1 X2
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X1 (M.op sF0 x))
       have i₂ := eq57 sF0 X1 x
       grind)
    | exact superpose eq57 eq215
    | exact resolve eq215 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq566 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op x y))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq54
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq54 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq609 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq57
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq57 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq79
  have eq7302 : (τ (k (σ y) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq7333 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq89 eq7302
    | exact resolve eq7302 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7302
  have eq7336 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq7333
       have r₂ := eq13 y y
       grind)
    | exact resolve eq7333 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7333
  have eq7337 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq7336
       grind)
    | exact superpose eq7336 eq77
    | exact resolve eq77 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7427 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq172
    | (have j0 := eq172 x
       grind)
    | exact resolve eq172 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq7452 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7427
  have eq7462 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7452
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq7452
    | exact resolve eq7452 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7452
  have eq7481 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7462
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq7462 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7462
  have eq7485 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq7481 eq50
    | exact resolve eq50 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7725 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq194
    | (have j0 := eq194 y
       grind)
    | exact resolve eq194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq7752 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq7725
  have eq7759 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7752
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq7752
    | exact resolve eq7752 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7752
  have eq7785 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq7759
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq7759 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7759
  have eq7806 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq7785 eq89
    | exact resolve eq89 eq7785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq7822 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7806
       have i₂ := eq7336
       grind)
    | exact superpose eq7336 eq7806
    | exact resolve eq7806 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336 eq7806
  have eq7937 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq209
    | (have j0 := eq209 (M.op x y)
       grind)
    | exact resolve eq209 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq7959 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7937
  have eq7964 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq7959
    | exact resolve eq7959 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7959
  have eq7995 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq7964
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq7964 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7964
  have eq8047 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq7995 eq157
    | exact resolve eq157 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq8264 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq338 X0 X1 X2
       have i₂ := eq343 (M.op X0 (M.op X1 X2)) X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq338 X1 x y
       have i₂ := eq343 (M.op X1 (M.op x y)) X1 X2
       grind)
    | exact superpose eq343 eq338
    | (have j0 := eq338 X0 X1 X2
       grind)
    | (have r₁ := eq338 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 (M.op x y))) X2
       have r₂ := eq343 X0 X1 X2
       grind)
    | (have r₁ := eq338 (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 X2)) X2
       have r₂ := eq343 X0 X1 X2
       grind)
    | exact resolve eq338 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq343
  have eq8342 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq8264 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8264
  have eq9603 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq7481 eq112
    | exact resolve eq112 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq10134 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7995 eq158
    | exact resolve eq158 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq17279 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq609 X0 X0
       have i₂ := eq56 X0 X0 X0
       grind)
    | exact superpose eq56 eq609
    | exact resolve eq609 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq20361 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq9603
       grind)
    | exact superpose eq9603 eq16
    | exact resolve eq16 eq9603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9603
  have eq20431 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq7485 eq20361
    | exact resolve eq20361 eq7485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20361
  have eq20441 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq20431
       have r₂ := eq13 x x
       grind)
    | exact resolve eq20431 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20431
  have eq20444 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20441
       grind)
    | exact superpose eq20441 eq44
    | exact resolve eq44 eq20441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq20477 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq7481 eq20444
    | exact resolve eq20444 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481 eq20444
  have eq22169 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10134 eq16
    | exact resolve eq16 eq10134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10134
  have eq22241 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8047 eq22169
    | exact resolve eq22169 eq8047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22169
  have eq22255 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq22241
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq22241 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22241
  have eq22258 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq22255 eq134
    | exact resolve eq134 eq22255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq22291 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq7995 eq22258
    | exact resolve eq22258 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995 eq22258
  have eq28814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq28814
    | exact resolve eq28814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28814
  have eq28826 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq28815
       have r₂ := eq28
       grind)
    | exact resolve eq28815 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28815
  have eq28830 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28826 eq7485
    | exact resolve eq7485 eq28826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28826
  have eq28898 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq28830
       have i₂ := eq20441
       grind)
    | exact superpose eq20441 eq28830
    | exact resolve eq28830 eq20441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28830
  have eq28905 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq28898
    | exact resolve eq28898 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28898
  have eq28906 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq28905
  have eq28915 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28906 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28906
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq28906
       grind)
    | exact resolve eq13 eq28906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28906
  have eq28947 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq28915
  have eq33431 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28947 eq84
    | exact resolve eq84 eq28947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33432 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28947 eq116
    | exact resolve eq116 eq28947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq28947
  have eq33447 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq33432
  have eq33456 : (k y x) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7822 eq33431
    | exact resolve eq33431 eq7822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7822 eq33431
  have eq33459 : (k y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq33456
       have r₂ := eq13 y x
       grind)
    | exact resolve eq33456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33456
  have eq33474 : (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq566 y x
       have i₂ := eq33459
       grind)
    | exact superpose eq33459 eq566
    | (have j0 := eq566 y x
       grind)
    | exact resolve eq566 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33477 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq33459
       grind)
    | exact superpose eq33459 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq33459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33459
  have eq33478 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq33477
  have eq33480 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq33478
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33478
    | exact resolve eq33478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33478
  have eq33483 : (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33474
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33474
    | exact resolve eq33474 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33474
  have eq33498 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33483
       have i₂ := eq7337
       grind)
    | exact superpose eq7337 eq33483
    | exact resolve eq33483 eq7337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7337 eq33483
  have eq33506 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7785 eq33498
    | exact resolve eq33498 eq7785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7785 eq33498
  have eq33511 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq54 eq33506
    | exact resolve eq33506 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33506
  have eq33516 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33511
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33511
    | exact resolve eq33511 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33511
  have eq33521 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33516
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33516
    | exact resolve eq33516 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33516
  have eq33526 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33521
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33521
    | exact resolve eq33521 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33521
  have eq33531 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33526
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33526
    | exact resolve eq33526 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33526
  have eq33534 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33531
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33531
    | exact resolve eq33531 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33531
  have eq33584 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq33447 eq290
    | exact resolve eq290 eq33447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33447
  have eq33664 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq239 y
       have i₂ := eq33480
       grind)
    | exact superpose eq33480 eq239
    | exact resolve eq239 eq33480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq33480
  have eq33713 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq348 eq33664
    | exact resolve eq33664 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq33664
  have eq34763 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20477
       have i₂ := eq33713
       grind)
    | exact superpose eq33713 eq20477
    | exact resolve eq20477 eq33713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33713
  have eq34822 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq34763
    | exact resolve eq34763 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34763
  have eq36598 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq34822 eq299
    | exact resolve eq299 eq34822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53805 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq36598 eq33584
    | exact resolve eq33584 eq36598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33584 eq36598
  have eq53898 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq53805
  have eq54305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq53898 eq34822
    | exact resolve eq34822 eq53898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34822 eq53898
  have eq54358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq54305
  have eq54384 : y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq54358
       have r₂ := eq28
       grind)
    | exact resolve eq54358 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54358
  have eq54403 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20477
       have i₂ := eq54384
       grind)
    | exact superpose eq54384 eq20477
    | exact resolve eq20477 eq54384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54411 : x = (M.op y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq296 x
       have i₂ := eq54384
       grind)
    | exact superpose eq54384 eq296
    | exact resolve eq296 eq54384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54447 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq8342 x x
       have i₂ := eq54384
       grind)
    | exact superpose eq54384 eq8342
    | exact resolve eq8342 eq54384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8342 eq54384
  have eq54463 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq249 eq54447
    | exact resolve eq54447 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq54447
  have eq54475 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54403
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54403
    | exact resolve eq54403 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54403
  have eq54483 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54463
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54463
    | exact resolve eq54463 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq54463
  have eq54858 : x = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq54411 eq211
    | exact resolve eq211 eq54411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55913 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq54475 eq56
    | exact resolve eq56 eq54475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61760 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq54483 eq566
    | (have j0 := eq566 (M.op x y) x
       grind)
    | exact resolve eq566 eq54483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq61772 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq61760
    | exact resolve eq61760 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61760
  have eq61786 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22291 eq61772
    | exact resolve eq61772 eq22291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22291 eq61772
  have eq61791 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq54 eq61786
    | exact resolve eq61786 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq61786
  have eq61796 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq61791
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61791
    | exact resolve eq61791 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61791
  have eq61801 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq61796
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61796
    | exact resolve eq61796 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61796
  have eq61806 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq61801
    | exact resolve eq61801 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61801
  have eq61811 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq61806
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61806
    | exact resolve eq61806 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61806
  have eq61814 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq61811
    | exact resolve eq61811 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61811
  have eq475726 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq33534 eq7485
    | exact resolve eq7485 eq33534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33534
  have eq475898 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq475726
       have i₂ := eq20441
       grind)
    | exact superpose eq20441 eq475726
    | exact resolve eq475726 eq20441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475726
  have eq475911 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq475898
    | exact resolve eq475898 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475898
  have eq475912 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq475911
  have eq475938 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq475912 eq290
    | exact resolve eq290 eq475912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq475944 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq475912 eq299
    | exact resolve eq299 eq475912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq475912
  have eq476032 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq318 eq475938
    | (have j0 := eq475938 (σ y)
       grind)
    | exact resolve eq475938 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq475938
  have eq476755 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq476032 eq475944
    | exact resolve eq475944 eq476032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475944 eq476032
  have eq476836 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq476755
  have eq476866 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20477
       have i₂ := eq476836
       grind)
    | exact superpose eq476836 eq20477
    | exact resolve eq20477 eq476836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20477 eq476836
  have eq477012 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq476866
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq476866
    | exact resolve eq476866 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476866
  have eq477409 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq477012 eq17279
    | exact resolve eq17279 eq477012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17279 eq477012
  have eq477509 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq477409
    | exact resolve eq477409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477409
  have eq477510 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq477509
  have eq480879 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq477510 eq84
    | exact resolve eq84 eq477510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq477510
  have eq480971 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq480879
    | exact resolve eq480879 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480879
  have eq1277770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq61814 eq55913
    | exact resolve eq55913 eq61814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55913 eq61814
  have eq1277898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1277770
  have eq1277921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq1277898
    | exact resolve eq1277898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277898
  have eq1277929 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1277921
       have r₂ := eq28
       grind)
    | exact resolve eq1277921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277921
  have eq1277968 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1277929 eq54475
    | exact resolve eq54475 eq1277929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54475 eq1277929
  have eq1278264 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1277968
  have eq1278357 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq287 x X0
       have i₂ := eq1278264
       grind)
    | exact superpose eq1278264 eq287
    | exact resolve eq287 eq1278264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278361 : y = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq296 y
       have i₂ := eq1278264
       grind)
    | exact superpose eq1278264 eq296
    | exact resolve eq296 eq1278264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278264
  have eq1278510 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1278357 x
       have i₂ := eq284 x x
       grind)
    | (have i₁ := eq1278357 y
       have i₂ := eq284 x x
       grind)
    | exact superpose eq284 eq1278357
    | (have j0 := eq1278357 y
       grind)
    | exact resolve eq1278357 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278357
  have eq1278986 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1278510 eq1278361
    | exact resolve eq1278361 eq1278510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278361 eq1278510
  have eq1279141 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1278986
  have eq1279176 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1279141 eq30
    | exact resolve eq30 eq1279141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1279141
  have eq1280477 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31 eq1279176
    | exact resolve eq1279176 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279176
  have eq1280478 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1280477
  have eq1280587 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1280478 eq29
    | exact resolve eq29 eq1280478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280686 : (k x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1280478 eq7485
    | exact resolve eq7485 eq1280478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7485 eq1280478
  have eq1281671 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8047 eq1280686
    | exact resolve eq1280686 eq8047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280686
  have eq1281747 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1280587
    | exact resolve eq1280587 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280587
  have eq1281766 : (k x x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22255 eq1281671
    | exact resolve eq1281671 eq22255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281671
  have eq1281816 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1281766
       have i₂ := eq20441
       grind)
    | exact superpose eq20441 eq1281766
    | exact resolve eq1281766 eq20441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20441 eq1281766
  have eq1282457 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1281747
  have eq1287465 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (M.op x x) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1281816 eq280
    | exact resolve eq280 eq1281816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281816
  have eq1287611 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1287465 X0 x
       have i₂ := eq280 X0 x x x
       grind)
    | exact superpose eq280 eq1287465
    | exact resolve eq1287465 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq1287465
  have eq1300106 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1287611 eq54411
    | exact resolve eq54411 eq1287611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54411 eq1287611
  have eq1300213 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1300106
  have eq1300313 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq287 x X0
       have i₂ := eq1300213
       grind)
    | exact superpose eq1300213 eq287
    | exact resolve eq287 eq1300213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq1300316 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq296 y
       have i₂ := eq1300213
       grind)
    | exact superpose eq1300213 eq296
    | exact resolve eq296 eq1300213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq1300213
  have eq1300469 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1300313 x
       have i₂ := eq284 x x
       grind)
    | (have i₁ := eq1300313 y
       have i₂ := eq284 x x
       grind)
    | exact superpose eq284 eq1300313
    | (have j0 := eq1300313 y
       grind)
    | exact resolve eq1300313 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq1300313
  have eq1301721 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1300469 eq1300316
    | exact resolve eq1300316 eq1300469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300316 eq1300469
  have eq1301879 : y = (M.op x y) := by grind
  clear eq1301721
  have eq1301918 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1301879 eq21
    | exact resolve eq21 eq1301879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1301969 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1301879 eq211
    | exact resolve eq211 eq1301879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq1302273 : (k y x) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1301879 eq54483
    | exact resolve eq54483 eq1301879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54483
  have eq1302274 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1301879 eq54858
    | exact resolve eq54858 eq1301879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54858
  have eq1302522 : x = (M.op y x) := by grind
  clear eq1302274
  have eq1302648 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1302273
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1302273 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302273
  have eq1302834 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1301918
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1301918
    | exact resolve eq1301918 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301918
  have eq1302938 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1302834 eq27
    | exact resolve eq27 eq1302834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1305861 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq480971
       have i₂ := eq1302648
       grind)
    | exact superpose eq1302648 eq480971
    | exact resolve eq480971 eq1302648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480971 eq1302648
  have eq1306048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1302834 eq1305861
    | exact resolve eq1305861 eq1302834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305861
  have eq1306161 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1306048
       have r₂ := eq28
       grind)
    | exact resolve eq1306048 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306048
  have eq1306272 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1302834 eq1306161
    | exact resolve eq1306161 eq1302834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306161
  have eq1311412 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y y
       have i₂ := eq1306272
       grind)
    | exact superpose eq1306272 eq56
    | exact resolve eq56 eq1306272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1306272
  have eq1311568 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1311412 x
       have i₂ := eq1301969 x
       grind)
    | exact superpose eq1301969 eq1311412
    | exact resolve eq1311412 eq1301969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301969 eq1311412
  have eq1311875 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1311568 eq29
    | exact resolve eq29 eq1311568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1311568
  have eq1313021 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1311875
    | exact resolve eq1311875 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1311875
  have eq1313141 : x = (M.op x y) := by
    first
    | (have r₁ := eq1313021
       have r₂ := eq1282457
       grind)
    | exact resolve eq1313021 eq1282457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282457 eq1313021
  have eq1313234 : x = y := by
    first
    | exact superpose eq1301879 eq1313141
    | exact resolve eq1313141 eq1301879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313141
  have eq1313420 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1313234
       grind)
    | exact superpose eq1313234 eq25
    | exact resolve eq25 eq1313234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1314205 : x = (M.op x x) := by
    first
    | (have i₁ := eq1302522
       have i₂ := eq1313234
       grind)
    | exact superpose eq1313234 eq1302522
    | exact resolve eq1302522 eq1313234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302522
  have eq1314862 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1302834 eq1313420
    | exact resolve eq1313420 eq1302834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302834 eq1313420
  have eq1315393 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1314862
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1314862
    | exact resolve eq1314862 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314862
  have eq1317207 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1315393 eq1302938
    | exact resolve eq1302938 eq1315393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302938
  have eq1318429 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1317207 eq8047
    | exact resolve eq8047 eq1317207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8047 eq1317207
  have eq1318691 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22255 eq1318429
    | exact resolve eq1318429 eq22255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22255 eq1318429
  have eq1318762 : (M.op y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1301879 eq1318691
    | exact resolve eq1318691 eq1301879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301879 eq1318691
  have eq1318805 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1318762
       have i₂ := eq1313234
       grind)
    | exact superpose eq1313234 eq1318762
    | exact resolve eq1318762 eq1313234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313234 eq1318762
  have eq1318836 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1318805
       have i₂ := eq1314205
       grind)
    | exact superpose eq1314205 eq1318805
    | exact resolve eq1318805 eq1314205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314205 eq1318805
  have eq1318870 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1318836 eq15
    | exact resolve eq15 eq1318836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318836
  have eq1319734 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1318870
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1318870
    | exact resolve eq1318870 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1318870
  have eq1320040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1315393 eq1319734
    | exact resolve eq1319734 eq1315393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315393 eq1319734
  have eq1320193 : False := by grind
  exact eq1320193

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pxx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
       have r₂ := eq12 x x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
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
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq53
    | exact resolve eq53 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq53
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
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
  have eq208 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X2 (σ X1)))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq62 X1 X0
       grind)
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | (have j1 := eq62 X1 X0
       grind)
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq62 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq230 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq231 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq235 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq231
    | (have j0 := eq231 X0 X1
       grind)
    | exact resolve eq231 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq231
  have eq244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq728 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq86 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq86 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1066 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq728 X0 x X1
       grind)
    | exact superpose eq728 eq9
    | exact resolve eq9 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq2908 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq244 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq244
    | (have j0 := eq244 (τ X0) (τ X1)
       grind)
    | exact resolve eq244 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq244
  have eq3093 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2908 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2908
    | (have j0 := eq2908 X0 X1
       grind)
    | exact resolve eq2908 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq3125 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3093 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq3093
    | (have j0 := eq3093 X0 X1
       grind)
    | exact resolve eq3093 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq3093
  have eq3144 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3125 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3125
    | (have j0 := eq3125 X0 X1
       grind)
    | exact resolve eq3125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125
  have eq3156 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3144 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3144
    | (have j0 := eq3144 X0 X1
       grind)
    | exact resolve eq3144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3144
  have eq3164 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3156 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3156
    | (have j0 := eq3156 X0 X1
       grind)
    | exact resolve eq3156 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3167 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3164 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3164
    | (have j0 := eq3164 X0 X1
       grind)
    | exact resolve eq3164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3164
  have eq3169 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3167 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3167
    | (have j0 := eq3167 X0 X1
       grind)
    | exact resolve eq3167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3170 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3169 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq3169 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq3169 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3308 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3377 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq228
    | exact resolve eq228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq3395 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3377 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3377
    | (have j0 := eq3377 X0 X1
       grind)
    | exact resolve eq3377 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq3399 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3395 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3395
    | (have j0 := eq3395 X0 X1
       grind)
    | exact resolve eq3395 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq3403 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3399 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq3399 (σ X1) X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq3399 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq3399 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq4062 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq208
    | exact resolve eq208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq4175 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4062 X0 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq4062
    | (have j0 := eq4062 X0 X1 X2
       grind)
    | exact resolve eq4062 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4062
  have eq4183 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) X0) (M.op X2 (M.op X2 X0))) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4175 X0 X1 X2
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq4175 X0 X1 X2
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq4175 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175
  have eq38610 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3403 X0 X1
       have i₂ := eq3170 X0 (σ X1)
       grind)
    | exact superpose eq3170 eq3403
    | (have j0 := eq3403 X0 X1
       have j1 := eq3170 X0 (σ X1)
       grind)
    | (have r₁ := eq3403 (σ X1) X1
       have r₂ := eq3170 (σ X1) (σ X1)
       grind)
    | exact resolve eq3403 eq3170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170 eq3403
  have eq38618 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38610 X0 X1
       have j1 := eq3308 X0 (σ X1)
       grind)
    | (have r₁ := eq38610 (σ X1) X1
       have r₂ := eq3308 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq38610 X0 X1
       have r₂ := eq3308 X0 (σ X1)
       grind)
    | exact resolve eq38610 eq3308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308 eq38610
  have eq56093 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 (σ X1) (M.op x (M.op x X0))
       have i₂ := eq4183 X0 X1 x
       grind)
    | exact superpose eq4183 eq1066
    | (have j1 := eq4183 X0 X1 x
       grind)
    | exact resolve eq1066 eq4183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq4183
  have eq56416 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq56093 X0 X1
       have j1 := eq38618 X0 X1
       grind)
    | (have r₁ := eq56093 X0 X1
       have r₂ := eq38618 X0 X1
       grind)
    | (have r₁ := eq56093 (σ X1) X1
       have r₂ := eq38618 (σ X1) X1
       grind)
    | exact resolve eq56093 eq38618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38618 eq56093
  have eq56520 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56416 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56416
    | exact resolve eq56416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq56416 (σ X0) X1
       grind)
    | exact superpose eq56416 eq15
    | exact resolve eq15 eq56416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56416
  have eq58965 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56567 x y
       grind)
    | exact superpose eq56567 eq16
    | exact resolve eq16 eq56567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56567
  have eq59449 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq58965
       have i₂ := eq56520 y x
       grind)
    | exact superpose eq56520 eq58965
    | exact resolve eq58965 eq56520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56520 eq58965
  have eq59450 : False := by grind
  exact eq59450

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyy_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq78 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 (M.op (M.op X1 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X0
       have i₂ := eq66 X1 X0 X2
       grind)
    | (have i₁ := eq9 X0 X1 (M.op X0 X2)
       have i₂ := eq66 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq119 (σ X0)
       grind)
    | exact superpose eq119 eq15
    | exact resolve eq15 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq119 (τ X0)
       grind)
    | exact superpose eq119 eq18
    | exact resolve eq18 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq128 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq128
    | exact resolve eq128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq135 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq124
    | exact resolve eq124 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq139 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq131
    | exact resolve eq131 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq131
  have eq145 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq9
    | exact resolve eq9 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) X1 (σ X0)
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq66
    | exact resolve eq66 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 X2 (σ X0) (σ X0) X1
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq78
    | exact resolve eq78 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq10
    | exact resolve eq10 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq413 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X0) X3) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq413 X0 X1 X2
       have i₂ := eq66 (M.op X2 X0) (M.op X0 X1) X3
       grind)
    | exact superpose eq66 eq413
    | exact resolve eq413 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq413 X0 x X1
       grind)
    | exact superpose eq413 eq9
    | exact resolve eq9 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq549 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq520 (σ X0) (σ X0) x
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq520
    | exact resolve eq520 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq520 (τ X0) (τ X0) x
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq520
    | exact resolve eq520 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq695 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 (M.op x (M.op x x)) X1
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq549
    | exact resolve eq549 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq797 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq145 (M.op X0 (M.op X0 X0)) (M.op (σ X0) X1)
       have i₂ := eq695 X0 X1
       grind)
    | exact superpose eq695 eq145
    | exact resolve eq145 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq695
  have eq813 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq797 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq797
    | exact resolve eq797 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq818 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq813 X0 x
       have i₂ := eq66 (σ X0) (σ X0) x
       grind)
    | exact superpose eq66 eq813
    | exact resolve eq813 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq813
  have eq819 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq818 X0
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq818
    | exact resolve eq818 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq3317 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3318 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3317 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3317
    | (have j0 := eq3317 (σ X0) (σ X1)
       grind)
    | exact resolve eq3317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq5575 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X2 (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq3318 X0 X1
       grind)
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq3318 X0 X1
       grind)
    | exact superpose eq3318 eq9
    | (have j1 := eq3318 X0 X1
       grind)
    | exact resolve eq9 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5577 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq3318 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq3318 X0 X1
       grind)
    | exact superpose eq3318 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq3318 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq3318 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq3318 X0 X0
       grind)
    | exact resolve eq12 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq5625 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5577 X0 X1
       have i₂ := eq135 X1
       grind)
    | exact superpose eq135 eq5577
    | (have j0 := eq5577 X0 X1
       grind)
    | exact resolve eq5577 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5577
  have eq5654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5625 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5625
    | (have j0 := eq5625 X0 X1
       grind)
    | exact resolve eq5625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5625
  have eq5655 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq24137 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5655 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5655
    | exact resolve eq5655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655
  have eq24162 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) ≠ (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24137 X0 X1
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq24137
    | (have j0 := eq24137 X0 X1
       grind)
    | exact resolve eq24137 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24137
  have eq24171 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24162 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq24162
    | (have j0 := eq24162 X0 X1
       grind)
    | (have r₁ := eq24162 (σ X1) X1
       have r₂ := eq11 (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq24162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24162
  have eq24177 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24171 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq24171
    | (have j0 := eq24171 X0 X1
       grind)
    | exact resolve eq24171 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24171
  have eq25346 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24177 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24177
    | exact resolve eq24177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24177
  have eq25469 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (k (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25346 (M.op (τ (M.op X0 X0)) X1) (τ X0)
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq25346
    | exact resolve eq25346 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq25346
  have eq25509 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq25469 X0 X1
       grind)
    | (have r₁ := eq25469 X0 X1
       have r₂ := eq163 X0
       grind)
    | exact resolve eq25469 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq25469
  have eq25569 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25509 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) X1
       have i₂ := eq151 X0 (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)
       grind)
    | exact superpose eq151 eq25509
    | exact resolve eq25509 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq25509
  have eq25665 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25569 X0 X1
       have i₂ := eq149 X0 (σ X0)
       grind)
    | exact superpose eq149 eq25569
    | exact resolve eq25569 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq25569
  have eq25671 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (τ (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25665 X0 X1
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq25665
    | exact resolve eq25665 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq25665
  have eq25673 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (τ (σ (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25671 X0 X1
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq25671
    | exact resolve eq25671 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq25671
  have eq25674 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25673 X0 X1
       have i₂ := eq10 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq10 eq25673
    | exact resolve eq25673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25673
  have eq25675 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25674 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25674
    | exact resolve eq25674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25674
  have eq25827 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25675 (M.op X0 X1) (M.op (M.op (M.op x X0) x) (M.op x X0))
       have i₂ := eq516 X0 X1 x x
       grind)
    | exact superpose eq516 eq25675
    | exact resolve eq25675 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq25675
  have eq26005 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25827 X0 X1
       have i₂ := eq67 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq25827
    | exact resolve eq25827 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq25827
  have eq46432 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26005 (σ X1) (σ X0)
       have i₂ := eq5575 X1 X0 (σ X1)
       grind)
    | exact superpose eq5575 eq26005
    | (have j1 := eq5575 X1 X0 x
       grind)
    | exact resolve eq26005 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5575 eq26005
  have eq46580 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46432 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq46432
    | (have j0 := eq46432 X0 X1
       grind)
    | exact resolve eq46432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46432
  have eq46581 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq46580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46580
  have eq46609 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq46581 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46581
  have eq46656 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46609 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq46609
    | exact resolve eq46609 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq46728 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46656 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq46656
    | exact resolve eq46656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46656
  have eq46746 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46728 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46728
    | exact resolve eq46728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46728
  have eq46762 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46746 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq46746
    | exact resolve eq46746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46746
  have eq46769 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46609 X0 X1
       have i₂ := eq46762 X1 X0
       grind)
    | exact superpose eq46762 eq46609
    | exact resolve eq46609 eq46762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46609 eq46762
  have eq47358 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46769 y x
       grind)
    | exact superpose eq46769 eq16
    | (have r₁ := eq16
       have r₂ := eq46769 y x
       grind)
    | exact resolve eq16 eq46769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46769
  have eq47533 : False := by grind
  exact eq47533

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq33 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq29
    | (have j0 := eq29 (M.op x y)
       grind)
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  have eq61 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
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
  have eq99 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq101 : ∀ X0 : G, x ≠ (M.op X0 (M.op X0 x)) ∨ (M.op (M.op X0 (M.op X0 x)) (M.op x y)) = (k (M.op X0 (M.op X0 x)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 x)) (M.op x y)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
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
  have eq275 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq82 eq54
    | exact resolve eq54 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq276 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq276 X0
       grind)
    | (have i₁ := eq53 (M.op x y)
       have i₂ := eq276 (M.op x y)
       grind)
    | exact superpose eq276 eq53
    | exact resolve eq53 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op X0 (M.op X0 (M.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x X0
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq54
    | exact resolve eq54 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq357 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq363 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq33
       have i₂ := eq14 sF1 sF1
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq372 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq375 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq368
  have eq376 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq363
  have eq380 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq372
    | exact resolve eq372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq441 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X1) (M.op X0 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq275 eq9
    | exact resolve eq9 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1382 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq375
       grind)
    | exact superpose eq375 eq10
    | exact resolve eq10 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq376 eq10
    | exact resolve eq10 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1640 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq357
    | (have j0 := eq357 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq357 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4812 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) x)) = (M.op (M.op x y) (M.op X0 (M.op X0 (M.op X0 (M.op X0 x))))) := by
    intro X0
    first
    | exact superpose eq307 eq271
    | exact resolve eq271 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq4922 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 X0
       have i₂ := eq271 X1 X2 X0
       grind)
    | (have i₁ := eq54 X0 X1 X0
       have i₂ := eq271 X0 X1 X0
       grind)
    | exact superpose eq271 eq54
    | exact resolve eq54 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4986 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq271 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq271 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq271 eq9
    | exact resolve eq9 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5002 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq53 sF0
       have i₂ := eq271 sF0 x sF0
       grind)
    | (have i₁ := eq53 X0
       have i₂ := eq271 X0 x sF0
       grind)
    | exact superpose eq271 eq53
    | exact resolve eq53 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5007 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq89 sF2
       have i₂ := eq271 sF2 sF4 sF2
       grind)
    | (have i₁ := eq89 X0
       have i₂ := eq271 X0 sF4 sF2
       grind)
    | exact superpose eq271 eq89
    | exact resolve eq89 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq271
  have eq5096 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) x)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq4812 X0
       have i₂ := eq54 X0 x X0
       grind)
    | exact superpose eq54 eq4812
    | exact resolve eq4812 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4812
  have eq5289 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op (M.op x y) (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq5096 eq5096
    | exact resolve eq5096 eq5096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096
  have eq6489 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op X0 x)))) := by
    intro X0 X1
    first
    | exact superpose eq5289 eq4922
    | exact resolve eq4922 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922 eq5289
  have eq6943 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq4986 X0 x X1
       grind)
    | exact superpose eq4986 eq9
    | exact resolve eq9 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4986
  have eq36937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq380
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq380
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq380 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq36937
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36937
    | exact resolve eq36937 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36937
  have eq36966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq36963
    | exact resolve eq36963 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36963
  have eq36967 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq36966
       have r₂ := eq28
       grind)
    | exact resolve eq36966 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36966
  have eq37002 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq36967 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq36967
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq36967
       grind)
    | exact resolve eq12 eq36967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36967
  have eq37028 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq37002
  have eq37040 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq67 eq37028
    | exact resolve eq37028 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37028
  have eq37052 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq37040
    | exact resolve eq37040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37040
  have eq37133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq37052
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq37052
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq37052 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37052
  have eq37153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq37133
  have eq37160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq37153
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37153
    | exact resolve eq37153 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37153
  have eq37163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq37160
    | exact resolve eq37160 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37160
  have eq37164 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq37163
       have r₂ := eq28
       grind)
    | exact resolve eq37163 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37163
  have eq37165 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq37164 eq1382
    | exact resolve eq1382 eq37164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37191 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  have eq37231 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq67 eq37191
    | exact resolve eq37191 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37191
  have eq37240 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq40 eq37165
    | exact resolve eq37165 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37165
  have eq38741 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq37240
       grind)
    | exact superpose eq37240 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq37240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37240
  have eq38743 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq38741
  have eq38776 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) x))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6489 y X0
       have i₂ := eq38743
       grind)
    | exact superpose eq38743 eq6489
    | exact resolve eq6489 eq38743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489 eq38743
  have eq38828 : x = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq295 eq38776
    | exact resolve eq38776 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq38776
  have eq49145 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq37231
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq37231
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq37231 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37231
  have eq49177 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq49145
  have eq49198 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq49177
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49177
    | exact resolve eq49177 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49177
  have eq49206 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq49198
    | exact resolve eq49198 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49198
  have eq49271 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq49206 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq49206
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq49206
       grind)
    | exact resolve eq12 eq49206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49206
  have eq49299 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq49271
  have eq49330 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq67 eq49299
    | exact resolve eq49299 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49299
  have eq49339 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq49330
    | exact resolve eq49330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49330
  have eq51965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq49339
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq49339
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq49339 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49339
  have eq51995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq51965
  have eq52008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq51995
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51995
    | exact resolve eq51995 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51995
  have eq52012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq52008
    | exact resolve eq52008 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52008
  have eq52014 : x = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq52012
       have r₂ := eq28
       grind)
    | exact resolve eq52012 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52012
  have eq52052 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq52014
       grind)
    | exact superpose eq52014 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq52014
       grind)
    | exact resolve eq12 eq52014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52014
  have eq52080 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq52052
  have eq52096 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq52080
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52080
    | exact resolve eq52080 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52080
  have eq52110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq380
       have i₂ := eq52096
       grind)
    | exact superpose eq52096 eq380
    | exact resolve eq380 eq52096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq52138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq52110
    | exact resolve eq52110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52110
  have eq52147 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq52138
       have r₂ := eq28
       grind)
    | exact resolve eq52138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52138
  have eq62151 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq52147 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq52147
       grind)
    | exact resolve eq12 eq52147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52147
  have eq62179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq62151
  have eq62210 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq67 eq62179
    | exact resolve eq62179 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62179
  have eq62223 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq62210
    | exact resolve eq62210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62210
  have eq99595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq62223
       have i₂ := eq52096
       grind)
    | exact superpose eq52096 eq62223
    | exact resolve eq62223 eq52096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62223
  have eq99647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq99595
  have eq99659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq99647
    | exact resolve eq99647 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99647
  have eq99667 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq99659
       have r₂ := eq28
       grind)
    | exact resolve eq99659 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99659
  have eq99720 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq99667
  have eq99788 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq67 eq99720
    | exact resolve eq99720 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99720
  have eq170666 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq99788
       have i₂ := eq52096
       grind)
    | exact superpose eq52096 eq99788
    | exact resolve eq99788 eq52096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99788
  have eq170733 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq170666
  have eq170756 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq170733
    | exact resolve eq170733 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170733
  have eq170757 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq170756
  have eq170840 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq170757 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq170757
       grind)
    | exact resolve eq12 eq170757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170757
  have eq170876 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq170840
  have eq170930 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq67 eq170876
    | exact resolve eq170876 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq170876
  have eq170940 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq170930
    | exact resolve eq170930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170930
  have eq174719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq170940
       have i₂ := eq52096
       grind)
    | exact superpose eq52096 eq170940
    | exact resolve eq170940 eq52096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52096 eq170940
  have eq174778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq174719
  have eq174790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq174778
    | exact resolve eq174778 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174778
  have eq174797 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq174790
       have r₂ := eq28
       grind)
    | exact resolve eq174790 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174790
  have eq175561 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq174797
       grind)
    | exact superpose eq174797 eq53
    | exact resolve eq53 eq174797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq175619 : x ≠ y ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq174797
       grind)
    | exact superpose eq174797 eq12
    | exact resolve eq12 eq174797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175638 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1640 x x
       have i₂ := eq174797
       grind)
    | exact superpose eq174797 eq1640
    | (have j0 := eq1640 x x
       grind)
    | exact resolve eq1640 eq174797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174797
  have eq175655 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq175638
  have eq175732 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq175655
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq175655
    | exact resolve eq175655 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175655
  have eq175755 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq175561
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq175561
    | exact resolve eq175561 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175561
  have eq175761 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq175732
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq175732
    | exact resolve eq175732 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175732
  have eq175773 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq175761
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq175761
    | exact resolve eq175761 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175761
  have eq175863 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq175755 eq12
    | exact resolve eq12 eq175755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175882 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq175755 eq1640
    | (have j0 := eq1640 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1640 eq175755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq175899 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq175882
  have eq175935 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq175899
    | exact resolve eq175899 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175899
  have eq175949 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq175935
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq175935
    | exact resolve eq175935 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175935
  have eq175953 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq175949
    | exact resolve eq175949 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175949
  have eq257837 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq175773 eq1382
    | exact resolve eq1382 eq175773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq257946 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq175773
  have eq257999 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq257837
       have r₂ := eq257946
       grind)
    | exact resolve eq257837 eq257946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257837 eq257946
  have eq258010 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40 eq257999
    | exact resolve eq257999 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257999
  have eq258013 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq258010
       have r₂ := eq175619
       grind)
    | exact resolve eq258010 eq175619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175619 eq258010
  have eq258127 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq375
       have i₂ := eq258013
       grind)
    | exact superpose eq258013 eq375
    | exact resolve eq375 eq258013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq258013
  have eq258150 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq258127
  have eq258163 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq258150
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq258150
    | exact resolve eq258150 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258150
  have eq258218 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq258163 eq59
    | exact resolve eq59 eq258163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq258163
  have eq258346 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq258218
    | exact resolve eq258218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258218
  have eq258387 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq258346 eq5007
    | exact resolve eq5007 eq258346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5007 eq258346
  have eq274663 : (k (M.op x y) (M.op x y)) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq175953 eq1393
    | exact resolve eq1393 eq175953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq175953
  have eq274711 : (k (M.op x y) (M.op x y)) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq274663
  have eq274716 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq274711
    | exact resolve eq274711 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274711
  have eq274717 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq274716
       have r₂ := eq175863
       grind)
    | exact resolve eq274716 eq175863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175863 eq274716
  have eq274719 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq274717 eq376
    | exact resolve eq376 eq274717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274717
  have eq274742 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq274719
  have eq274755 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq274742
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq274742
    | exact resolve eq274742 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274742
  have eq274811 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq274755 eq9
    | exact resolve eq9 eq274755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274845 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq274755 eq6943
    | exact resolve eq6943 eq274755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6943 eq274755
  have eq274901 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq274845
    | (have j0 := eq274845 (σ y)
       grind)
    | exact resolve eq274845 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274845
  have eq622031 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq274901 eq274811
    | exact resolve eq274811 eq274901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274811 eq274901
  have eq622142 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq622031
  have eq622153 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq278 eq622142
    | exact resolve eq622142 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq622142
  have eq622259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq622153 eq258387
    | exact resolve eq258387 eq622153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258387
  have eq622363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq622259
  have eq622379 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq622363
       have r₂ := eq28
       grind)
    | exact resolve eq622363 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622363
  have eq622399 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq622379 eq622153
    | exact resolve eq622153 eq622379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622153
  have eq622531 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq622399
  have eq622681 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq622531 eq622379
    | exact resolve eq622379 eq622531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622379 eq622531
  have eq622824 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq622681
  have eq622866 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq622824 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq622824
       grind)
    | exact resolve eq12 eq622824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622824
  have eq622897 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq622866
  have eq622903 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33 eq622897
    | exact resolve eq622897 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622897
  have eq622917 : (k (M.op x y) (M.op x y)) = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq622903 eq10
    | exact resolve eq10 eq622903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622903
  have eq623002 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38 eq622917
    | exact resolve eq622917 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622917
  have eq623017 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq623002 eq14
    | (have j0 := eq14 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq14 eq623002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623002
  have eq623022 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq623017
  have eq623080 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq623022 eq175755
    | exact resolve eq175755 eq623022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175755 eq623022
  have eq623515 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq623080
  have eq623622 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq623515 eq39
    | exact resolve eq39 eq623515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq623515
  have eq623776 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq623622
    | exact resolve eq623622 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623622
  have eq623777 : x = (M.op x y) := by grind
  clear eq623776
  have eq623781 : x = (M.op x y) := by
    first
    | exact superpose eq623777 eq19
    | exact resolve eq19 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq623782 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq623777 eq21
    | exact resolve eq21 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq623785 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k x x)) := by
    first
    | exact superpose eq623777 eq33
    | exact resolve eq33 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq623788 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq623777 eq38
    | exact resolve eq38 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq623792 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq623777 eq55
    | exact resolve eq55 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq623798 : x ≠ y ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq623777 eq99
    | exact resolve eq99 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq623800 : ∀ X0 : G, x ≠ (M.op X0 (M.op X0 x)) ∨ (M.op (M.op X0 (M.op X0 x)) x) = (k (M.op X0 (M.op X0 x)) x) := by
    intro X0
    first
    | exact superpose eq623777 eq101
    | (have j0 := eq101 X0
       grind)
    | exact resolve eq101 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq623818 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq623777 eq376
    | exact resolve eq376 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq623820 : ∀ X0 X1 : G, x = (M.op (M.op x X1) (M.op X0 (M.op x x))) := by
    intro X0 X1
    first
    | exact superpose eq623777 eq441
    | exact resolve eq441 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq624209 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq623777 eq5002
    | exact resolve eq5002 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq625295 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623777 eq38828
    | exact resolve eq38828 eq623777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38828 eq623777
  have eq641702 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq625295
  have eq644393 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq623782
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq623782
    | exact resolve eq623782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623782
  have eq645432 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq644393 eq23
    | exact resolve eq23 eq644393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq645433 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq644393 eq27
    | exact resolve eq27 eq644393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq646511 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq644393 eq37164
    | exact resolve eq37164 eq644393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37164
  have eq651987 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq644393 eq641702
    | exact resolve eq641702 eq644393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641702 eq644393
  have eq664642 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq624209 x
       have i₂ := eq651987
       grind)
    | exact superpose eq651987 eq624209
    | exact resolve eq624209 eq651987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624209 eq651987
  have eq664733 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq664642
       have i₂ := eq623781
       grind)
    | exact superpose eq623781 eq664642
    | exact resolve eq664642 eq623781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664642
  have eq664734 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq664733
  have eq664748 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq623792 X0
       have i₂ := eq664734
       grind)
    | exact superpose eq664734 eq623792
    | exact resolve eq623792 eq664734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623792
  have eq664757 : ∀ X0 : G, x = (M.op x (M.op X0 x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq623820 X0 x
       have i₂ := eq664734
       grind)
    | exact superpose eq664734 eq623820
    | exact resolve eq623820 eq664734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623820
  have eq664776 : x ≠ x ∨ x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq664734
       grind)
    | exact superpose eq664734 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq664734
       grind)
    | exact resolve eq12 eq664734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664734
  have eq664815 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq664776
  have eq664834 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq357 x x
       have i₂ := eq664815
       grind)
    | exact superpose eq664815 eq357
    | (have j0 := eq357 x x
       grind)
    | exact resolve eq357 eq664815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq664815
  have eq664845 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq664834
  have eq664853 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq664845
       have i₂ := eq645432
       grind)
    | exact superpose eq645432 eq664845
    | exact resolve eq664845 eq645432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664845
  have eq664881 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq664853 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq664853
       grind)
    | exact resolve eq12 eq664853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664920 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq664881
  have eq664932 : (σ (M.op x y)) = (σ (k x x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq623785 eq664920
    | exact resolve eq664920 eq623785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623785 eq664920
  have eq669076 : x ≠ x ∨ (k x x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq623800 x
       have i₂ := eq664757 x
       grind)
    | exact superpose eq664757 eq623800
    | (have r₁ := eq623800 x
       have r₂ := eq664757 x
       grind)
    | exact resolve eq623800 eq664757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623800 eq664757
  have eq669079 : (k x x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq669076
  have eq669108 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq664932
       have i₂ := eq669079
       grind)
    | exact superpose eq669079 eq664932
    | exact resolve eq664932 eq669079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664932 eq669079
  have eq669125 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq669108
  have eq744097 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq646511 eq664853
    | exact resolve eq664853 eq646511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646511 eq664853
  have eq744309 : x = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq744097
  have eq744431 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq664748 x
       have i₂ := eq744309
       grind)
    | exact superpose eq744309 eq664748
    | exact resolve eq664748 eq744309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664748 eq744309
  have eq744569 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq744431
  have eq744618 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq669125
       have i₂ := eq744569
       grind)
    | exact superpose eq744569 eq669125
    | exact resolve eq669125 eq744569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669125 eq744569
  have eq744978 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq744618
  have eq745097 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq744978
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq744978
    | exact resolve eq744978 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq744978
  have eq745098 : (σ (M.op x y)) = (σ y) := by grind
  clear eq745097
  have eq745117 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq745098 eq40
    | exact resolve eq40 eq745098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq747190 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq745098 eq645433
    | exact resolve eq645433 eq745098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645433 eq745098
  have eq749813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq747190 eq623818
    | exact resolve eq623818 eq747190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623818
  have eq750897 : x = y := by
    first
    | exact superpose eq623788 eq745117
    | exact resolve eq745117 eq623788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623788 eq745117
  have eq751564 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq749813
       have r₂ := eq28
       grind)
    | exact resolve eq749813 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749813
  have eq752471 : x = (M.op x x) := by
    first
    | (have i₁ := eq623781
       have i₂ := eq750897
       grind)
    | exact superpose eq750897 eq623781
    | exact resolve eq623781 eq750897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623781
  have eq752474 : (k x x) = (M.op x x) ∨ x ≠ y := by
    first
    | (have i₁ := eq623798
       have i₂ := eq750897
       grind)
    | exact superpose eq750897 eq623798
    | (have r₁ := eq623798
       have r₂ := eq750897
       grind)
    | exact resolve eq623798 eq750897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623798
  have eq755983 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
    first
    | exact superpose eq747190 eq751564
    | exact resolve eq751564 eq747190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747190 eq751564
  have eq757472 : (k x x) = (M.op x x) := by
    first
    | (have r₁ := eq752474
       have r₂ := eq750897
       grind)
    | exact resolve eq752474 eq750897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750897 eq752474
  have eq758532 : x = (k x x) := by
    first
    | (have i₁ := eq757472
       have i₂ := eq752471
       grind)
    | exact superpose eq752471 eq757472
    | exact resolve eq757472 eq752471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752471 eq757472
  have eq759239 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq755983
       have i₂ := eq758532
       grind)
    | exact superpose eq758532 eq755983
    | exact resolve eq755983 eq758532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755983 eq758532
  have eq759679 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq759239
       have i₂ := eq645432
       grind)
    | exact superpose eq645432 eq759239
    | exact resolve eq759239 eq645432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645432 eq759239
  have eq759938 : False := by grind
  exact eq759938

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X0 (k X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq55 X0 (M.op X0 X0)
       have r₂ := eq46 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq46 X0 (k X1 X0)
       grind)
    | exact resolve eq55 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq55
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq60
  have eq131 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq135 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq131 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq131 X1 X1
       have r₂ := eq64 X1 X1
       grind)
    | exact resolve eq131 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq131
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq135 (σ X1) (σ X0)
       grind)
    | exact superpose eq135 eq15
    | exact resolve eq15 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq135 X1 X0
       grind)
    | exact superpose eq135 eq255
    | exact resolve eq255 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq255
  have eq261 : False := by grind
  exact eq261

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
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
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq259 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq259
    | (have j0 := eq259 X0
       grind)
    | exact resolve eq259 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq259
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq274
    | (have j0 := eq274 X0
       grind)
    | exact resolve eq274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq277 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq277 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq277 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq285 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq278 (σ X0)
       grind)
    | exact superpose eq278 eq15
    | exact resolve eq15 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq285
    | exact resolve eq285 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq285
  have eq440 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq454 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1416 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1463 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1416 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1416
    | (have j0 := eq1416 X0 X1
       grind)
    | exact resolve eq1416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq2613 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq440
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq440
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq440
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq440
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq2614 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2613
  have eq50661 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2614
       grind)
    | exact superpose eq2614 eq16
    | exact resolve eq16 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614
  have eq50662 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq50661
       have r₂ := eq296 x
       grind)
    | exact resolve eq50661 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50661
  have eq66932 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq50662
       grind)
    | exact superpose eq50662 eq10
    | exact resolve eq10 eq50662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50662
  have eq67043 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66932
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66932
    | exact resolve eq66932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66932
  have eq67061 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67043
       grind)
    | exact superpose eq67043 eq16
    | exact resolve eq16 eq67043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67043
  have eq67062 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq67061
       have r₂ := eq296 x
       grind)
    | exact resolve eq67061 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67061
  have eq67690 : y ≠ y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq67062
       grind)
    | exact superpose eq67062 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq67062
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq67062
       grind)
    | exact resolve eq12 eq67062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67062
  have eq67797 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67690
  have eq67832 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq454 x y
       have i₂ := eq67797
       grind)
    | exact superpose eq67797 eq454
    | (have j0 := eq454 x y
       grind)
    | exact resolve eq454 eq67797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq67797
  have eq67837 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67832
  have eq67838 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67837
  have eq68818 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67838
       grind)
    | exact superpose eq67838 eq10
    | exact resolve eq10 eq67838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67838
  have eq68929 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68818
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq68818
    | exact resolve eq68818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68818
  have eq68947 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68929
       grind)
    | exact superpose eq68929 eq16
    | exact resolve eq16 eq68929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68929
  have eq68952 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq68947
       have r₂ := eq296 x
       grind)
    | exact resolve eq68947 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68947
  have eq69439 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68952
       grind)
    | exact superpose eq68952 eq16
    | exact resolve eq16 eq68952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69462 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq68952
       grind)
    | exact superpose eq68952 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq68952
       grind)
    | exact resolve eq12 eq68952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68952
  have eq69571 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq69462
  have eq69630 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq69571
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq69571
    | exact resolve eq69571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69571
  have eq70147 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1463 x y
       have i₂ := eq69630
       grind)
    | exact superpose eq69630 eq1463
    | (have j0 := eq1463 x y
       grind)
    | exact resolve eq1463 eq69630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq69630
  have eq70279 : x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq70147
       have r₂ := eq69439
       grind)
    | exact resolve eq70147 eq69439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70147
  have eq70672 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70279
       grind)
    | exact superpose eq70279 eq16
    | exact resolve eq16 eq70279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70279
  have eq70684 : y = (M.op x y) := by
    first
    | (have r₁ := eq70672
       have r₂ := eq296 x
       grind)
    | exact resolve eq70672 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq70672
  have eq70691 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq69439
       have i₂ := eq70684
       grind)
    | exact superpose eq70684 eq69439
    | exact resolve eq69439 eq70684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69439 eq70684
  have eq70805 : False := by grind
  exact eq70805

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
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
  have eq610 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq163
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq163
    | exact resolve eq163 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq611 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq610
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq610
    | exact resolve eq610 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq652 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq611
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq611
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq611 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq611
  have eq653 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq652
  have eq1801 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq10
    | exact resolve eq10 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq1837 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1801
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1801
    | exact resolve eq1801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1838 : (M.op y y) = (M.op x x) := by grind
  clear eq1837
  have eq1963 : ∀ X0 : G, y = (M.op (M.op x x) (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq1838
       grind)
    | exact superpose eq1838 eq9
    | exact resolve eq9 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2012 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x x) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq1963 X0
       have i₂ := eq109 X0 y (M.op x x)
       grind)
    | (have i₁ := eq1963 (M.op x x)
       have i₂ := eq109 (M.op x x) y (M.op x x)
       grind)
    | exact superpose eq109 eq1963
    | exact resolve eq1963 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq2550 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq2012 y
       have i₂ := eq1838
       grind)
    | exact superpose eq1838 eq2012
    | exact resolve eq2012 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838 eq2012
  have eq2587 : y = (M.op (M.op x x) (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq2550
       have i₂ := eq109 x x (M.op x x)
       grind)
    | exact superpose eq109 eq2550
    | exact resolve eq2550 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq2550
  have eq2590 : x = y := by
    first
    | (have i₁ := eq2587
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq2587
    | exact resolve eq2587 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2593 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2590
       grind)
    | exact superpose eq2590 eq16
    | exact resolve eq16 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2601 : False := by grind
  exact eq2601
