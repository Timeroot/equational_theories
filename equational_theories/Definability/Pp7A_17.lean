import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq45 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq47
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq47
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq68
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq93 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq38
  have eq121 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq114
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (M.op x x) = (M.op x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq11 x (τ X0)
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x (τ X0)
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq238 eq14
    | exact resolve eq14 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq239 eq14
    | exact resolve eq14 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq331 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X0) X1 X2 (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op X0 X1) X1
       have i₂ := eq56 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X3 X1) (M.op X3 X1)) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X3 X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = (k (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq53 X1 X3 X0 X2
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X3 X1)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))
       have r₂ := eq53 X1 X1 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op (M.op X3 X1) (M.op X3 X1)) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq371 X0 X1 X2 X3
       have i₂ := eq56 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq56 eq371
    | (have j0 := eq371 X0 X1 X2 X3
       grind)
    | exact resolve eq371 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq456 : ∀ X0 : G, (M.op (k (σ x) (σ y)) (σ X0)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ (k (k x y) X0)) = (M.op (k (σ x) (σ y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq65 (k x y) x
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq65
    | exact resolve eq65 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq470 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq65 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq482 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq483 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq483
    | (have j0 := eq483 X0 X1
       grind)
    | exact resolve eq483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq2846 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq344 (M.op X0 X0) X1 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq344
    | exact resolve eq344 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2865 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq344
    | (have j0 := eq344 (σ y) X0 (σ x)
       grind)
    | exact resolve eq344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2888 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq344
    | exact resolve eq344 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2894 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X4 (M.op X3 X1)) (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X2 X0) X1 X2 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq344 X0 X1 X2
       grind)
    | exact superpose eq344 eq53
    | exact resolve eq53 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3044 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq349 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq349
    | exact resolve eq349 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq3063 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3044 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3044
    | exact resolve eq3044 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (σ x))) = (M.op (M.op X4 (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) (M.op (M.op X1 (M.op X0 (σ x))) (M.op X1 (M.op X0 (σ x))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq351 eq53
    | exact resolve eq53 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq3133 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq340 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq340
    | exact resolve eq340 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq3189 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq342 (M.op sF3 x) x
       have i₂ := eq56 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq56 eq342
    | exact resolve eq342 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3194 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 (M.op (σ y) X1))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq342 eq14
    | exact resolve eq14 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq3264 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq347 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq347
    | exact resolve eq347 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3315 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq347 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq347
    | exact resolve eq347 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4784 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq331
    | exact resolve eq331 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4785 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq331 X0 X1 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq53 X0 X0 X2 X3
       grind)
    | exact superpose eq53 eq331
    | exact resolve eq331 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq4786 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq331 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq344 X0 X1 X0
       grind)
    | exact superpose eq344 eq331
    | exact resolve eq331 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4790 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 (M.op X1 X4)) (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq331 (M.op X2 (M.op X0 X3)) X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq347 X0 X1 X2 X3 (M.op X2 (M.op X0 X3))
       grind)
    | exact superpose eq347 eq331
    | exact resolve eq331 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq4825 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq56 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq56 eq331
    | exact resolve eq331 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq5170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq5170
    | exact resolve eq5170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5170
  have eq5182 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq5171
       have r₂ := eq28
       grind)
    | exact resolve eq5171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq5186 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq5182
    | exact resolve eq5182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5182
  have eq5462 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5186 eq93
    | (have r₁ := eq93
       have r₂ := eq5186
       grind)
    | exact resolve eq93 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq5476 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5186 eq56
    | exact resolve eq56 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186
  have eq5483 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq5462
  have eq5484 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq5483
  have eq5608 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq484 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq484
    | (have j0 := eq484 X0 x
       grind)
    | exact resolve eq484 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq6020 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5476 eq256
    | exact resolve eq256 eq5476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq6159 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5484 eq73
    | exact resolve eq73 eq5484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq5484
  have eq6168 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6159
  have eq6190 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6168 eq56
    | exact resolve eq56 eq6168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6397 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq6190 eq14
    | exact resolve eq14 eq6190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6190
  have eq6608 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq346 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq54 (M.op X1 X2)
       grind)
    | exact superpose eq54 eq346
    | exact resolve eq346 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq6692 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6168 eq6020
    | exact resolve eq6020 eq6168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020 eq6168
  have eq6710 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq6692
  have eq9245 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) ∨ (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) = (k (σ x) (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1)))) ∨ (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq373
    | exact resolve eq373 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq373
  have eq11146 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6710 eq6397
    | exact resolve eq6397 eq6710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6397 eq6710
  have eq11202 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq11146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11146
  have eq11303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5476 eq11202
    | exact resolve eq11202 eq5476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476 eq11202
  have eq11333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11303
  have eq11339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq11333
    | exact resolve eq11333 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11333
  have eq11344 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11339
       have r₂ := eq28
       grind)
    | exact resolve eq11339 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq11365 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq11344
       grind)
    | exact superpose eq11344 eq56
    | exact resolve eq56 eq11344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11344
  have eq11414 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq11365 eq251
    | exact resolve eq251 eq11365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq11702 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq244 y X0 x
       have i₂ := eq11414 y
       grind)
    | exact superpose eq11414 eq244
    | exact resolve eq244 eq11414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq11414
  have eq13042 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11365 eq11702
    | exact resolve eq11702 eq11365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq13070 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13042
  have eq13075 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13070
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13070
    | exact resolve eq13070 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13070
  have eq13162 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq238
       have i₂ := eq13075
       grind)
    | exact superpose eq13075 eq238
    | exact resolve eq238 eq13075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq13075
  have eq13300 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13162 eq11365
    | exact resolve eq11365 eq13162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365 eq13162
  have eq13342 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq13300
  have eq13350 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13342 eq30
    | exact resolve eq30 eq13342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13342
  have eq13446 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq13350
    | exact resolve eq13350 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13350
  have eq13447 : x = y := by grind
  clear eq13446
  have eq13557 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13447
       grind)
    | exact superpose eq13447 eq19
    | exact resolve eq19 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13558 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13447
       grind)
    | exact superpose eq13447 eq25
    | exact resolve eq25 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq13656 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13558
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13558
    | exact resolve eq13558 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13558
  have eq13683 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13656 eq27
    | exact resolve eq27 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq13843 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq14
    | exact resolve eq14 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13853 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq56
    | exact resolve eq56 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14098 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13683 eq56
    | exact resolve eq56 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14363 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq13656 eq2865
    | exact resolve eq2865 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq14664 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq3133 X0
       have i₂ := eq13447
       grind)
    | exact superpose eq13447 eq3133
    | exact resolve eq3133 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq15094 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq13656 eq3189
    | exact resolve eq3189 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189
  have eq15109 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq15094 eq344
    | exact resolve eq344 eq15094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15284 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 (M.op (σ y) X1))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq14098 eq3194
    | exact resolve eq3194 eq14098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194
  have eq15285 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X2 (M.op X0 (M.op (σ x) X1))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq13656 eq15284
    | exact resolve eq15284 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15284
  have eq15696 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq14363 eq3315
    | exact resolve eq3315 eq14363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363
  have eq15962 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq14098 eq15696
    | exact resolve eq15696 eq14098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696
  have eq16677 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq4784 X0 x
       have i₂ := eq14664 X0
       grind)
    | (have i₁ := eq4784 y x
       have i₂ := eq14664 y
       grind)
    | exact superpose eq14664 eq4784
    | exact resolve eq4784 eq14664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14664
  have eq19185 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq16677 eq14
    | exact resolve eq14 eq16677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16677
  have eq20922 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3315 X0 (M.op x (M.op x (M.op X0 X1))) (M.op X0 X1) X1
       have i₂ := eq19185 (M.op X0 X1) x
       grind)
    | exact superpose eq19185 eq3315
    | exact resolve eq3315 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21041 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20922 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq20922
    | exact resolve eq20922 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20922
  have eq23252 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ x)) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 (σ x))))) (σ x)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq15962 eq368
    | exact resolve eq368 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq15962
  have eq23600 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X2 (σ x))))) (σ x)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq13683 eq23252
    | exact resolve eq23252 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23252
  have eq26480 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq15094 eq3264
    | exact resolve eq3264 eq15094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3264
  have eq33209 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op (σ x) X0) (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq15285 eq6608
    | exact resolve eq6608 eq15285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15285
  have eq33359 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6608 X0 X1 (M.op x (M.op x X0)) X0
       have i₂ := eq19185 X0 x
       grind)
    | exact superpose eq19185 eq6608
    | exact resolve eq6608 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq33967 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | exact superpose eq15094 eq33209
    | exact resolve eq33209 eq15094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15094 eq33209
  have eq35337 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x x)) ∨ (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3063 eq121
    | exact resolve eq121 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq35338 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35337
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq35337
    | exact resolve eq35337 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35337
  have eq35339 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq35338
    | exact resolve eq35338 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35338
  have eq35340 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13853 eq35339
    | exact resolve eq35339 eq13853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13853 eq35339
  have eq35341 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3063 eq35340
    | exact resolve eq35340 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063 eq35340
  have eq35342 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35341
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq35341
    | exact resolve eq35341 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35341
  have eq35343 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35342
  have eq43858 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 X0)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26480 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq26480
    | exact resolve eq26480 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26480
  have eq91352 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344 X0 X1 X2
       have i₂ := eq21041 X0 X1
       grind)
    | exact superpose eq21041 eq344
    | exact resolve eq344 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq91359 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4784 X0 X1
       have i₂ := eq21041 X0 X1
       grind)
    | exact superpose eq21041 eq4784
    | exact resolve eq4784 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq91361 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33359 X1 X0
       have i₂ := eq21041 X0 X1
       grind)
    | exact superpose eq21041 eq33359
    | exact resolve eq33359 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33359
  have eq95684 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3315 X1 X2 X3 (M.op X1 (M.op X0 X1))
       have i₂ := eq91359 X1 X0
       grind)
    | exact superpose eq91359 eq3315
    | exact resolve eq3315 eq91359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91359
  have eq113531 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2846 X0 X1
       have i₂ := eq21041 (M.op X0 X0) X1
       grind)
    | exact superpose eq21041 eq2846
    | exact resolve eq2846 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq113538 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq113531 (M.op X0 X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq113531
    | exact resolve eq113531 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq113531
  have eq123013 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4786 X0 X1 X2
       have i₂ := eq21041 (M.op X0 X1) X2
       grind)
    | exact superpose eq21041 eq4786
    | exact resolve eq4786 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4786
  have eq125541 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3315 X2 X3 X4 (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2)))
       have i₂ := eq123013 X1 X2 X0
       grind)
    | exact superpose eq123013 eq3315
    | exact resolve eq3315 eq123013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315 eq123013
  have eq128180 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4825 X0 X1
       have i₂ := eq21041 X1 (M.op X0 X0)
       grind)
    | exact superpose eq21041 eq4825
    | exact resolve eq4825 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825
  have eq128316 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128180 (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq345 X0 X1 X2 (M.op X2 X0)
       grind)
    | exact superpose eq345 eq128180
    | exact resolve eq128180 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq129220 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128316 X0 X1 X2
       have i₂ := eq243 (M.op X0 X1)
       grind)
    | exact superpose eq243 eq128316
    | exact resolve eq128316 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq128316
  have eq129385 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129220 X0 X1 X2
       have i₂ := eq21041 X1 X0
       grind)
    | exact superpose eq21041 eq129220
    | exact resolve eq129220 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129220
  have eq141922 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (M.op x y) = (M.op x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq199 X0
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq199
    | (have j0 := eq199 X0
       grind)
    | exact resolve eq199 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq141984 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (σ x) X0)) ∨ (M.op x y) = (M.op x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 (M.op x (τ X0))
       have i₂ := eq141922 X0
       grind)
    | exact superpose eq141922 eq16
    | (have j1 := eq141922 X0
       grind)
    | exact resolve eq16 eq141922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141922
  have eq147402 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k X0 x)) := by
    intro X0
    first
    | exact superpose eq13683 eq5608
    | (have j0 := eq5608 X0
       grind)
    | exact resolve eq5608 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608
  have eq147515 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq21 eq147402
    | (have j0 := eq147402 (M.op x y)
       grind)
    | exact resolve eq147402 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147402
  have eq147672 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq114 eq147515
    | exact resolve eq147515 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147515
  have eq147738 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq114 eq147672
    | exact resolve eq147672 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq147672
  have eq157114 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X4 (M.op X3 X1)) (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2894 X0 X1 X2 X3 X4
       have i₂ := eq21041 (M.op X0 X1) X2
       grind)
    | exact superpose eq21041 eq2894
    | exact resolve eq2894 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq158829 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq157114 X0 X1 (M.op X0 X1) X3 X2
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq157114
    | exact resolve eq157114 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157114
  have eq159050 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq158829 X0 X1 X2 X3
       have i₂ := eq21041 X1 X0
       grind)
    | exact superpose eq21041 eq158829
    | exact resolve eq158829 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158829
  have eq162285 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 (M.op X1 X4)) (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4790 X0 X1 X2 X3 X4
       have i₂ := eq21041 (M.op X0 X1) X2
       grind)
    | exact superpose eq21041 eq4790
    | exact resolve eq4790 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4790
  have eq163102 : ∀ X0 X2 X3 : G, (M.op X0 x) = (M.op (M.op X2 (M.op (M.op x x) X3)) (M.op x (M.op X0 x))) := by
    intro X0 X2 X3
    first
    | exact superpose eq51 eq162285
    | exact resolve eq162285 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq162285
  have eq164252 : ∀ X0 X2 X3 : G, (M.op X0 x) = (M.op (M.op X2 (M.op (M.op x y) X3)) (M.op x (M.op X0 x))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq163102 X0 X2 X3
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq163102
    | exact resolve eq163102 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163102
  have eq229042 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35343 eq147738
    | exact resolve eq147738 eq35343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35343 eq147738
  have eq229082 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq229042
       have r₂ := eq28
       grind)
    | exact resolve eq229042 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229042
  have eq229149 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229082 eq2888
    | exact resolve eq2888 eq229082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888
  have eq229237 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13683 eq229149
    | exact resolve eq229149 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229149
  have eq229281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229237 eq229082
    | exact resolve eq229082 eq229237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229082 eq229237
  have eq229408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq229281
  have eq229469 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq229408
       have r₂ := eq28
       grind)
    | exact resolve eq229408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229408
  have eq229874 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229469 eq29
    | exact resolve eq29 eq229469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq229469
  have eq230311 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq229874
    | exact resolve eq229874 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229874
  have eq230312 : x = (M.op x y) := by grind
  clear eq230311
  have eq230396 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq230312 eq21
    | exact resolve eq21 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq230537 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op x X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq230312 eq13843
    | exact resolve eq13843 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13843
  have eq230758 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq230396
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq230396
    | exact resolve eq230396 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230396
  have eq231044 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 (σ (M.op x y)))))) (σ (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq230758 eq23600
    | exact resolve eq23600 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23600
  have eq231205 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq231044 x x x x
       have i₂ := eq125541 x x sF1 x x
       grind)
    | exact superpose eq125541 eq231044
    | exact resolve eq231044 eq125541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125541 eq231044
  have eq232549 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (σ x))) = (M.op (M.op X4 (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) (M.op (M.op X0 (σ x)) (M.op X1 (M.op X0 (σ x))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3114 X0 X1 X2 X3 X4
       have i₂ := eq21041 (M.op X0 sF2) X1
       grind)
    | exact superpose eq21041 eq3114
    | exact resolve eq3114 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq232550 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (σ (M.op x y)))) = (M.op (M.op X4 (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (M.op X0 (σ (M.op x y)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq230758 eq232549
    | exact resolve eq232549 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232549
  have eq232921 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232550 sF1 sF1 X2 x x
       have i₂ := eq113538 sF1 sF1
       grind)
    | exact superpose eq113538 eq232550
    | exact resolve eq232550 eq113538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113538 eq232550
  have eq233199 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq231205 eq232921
    | exact resolve eq232921 eq231205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232921
  have eq233285 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq233199 x x x
       have i₂ := eq95684 x sF4 x x
       grind)
    | exact superpose eq95684 eq233199
    | exact resolve eq233199 eq95684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95684 eq233199
  have eq233337 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14098 eq233285
    | exact resolve eq233285 eq14098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14098 eq233285
  have eq233361 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230758 eq233337
    | exact resolve eq233337 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233337
  have eq233628 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq233361 eq33967
    | exact resolve eq33967 eq233361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33967
  have eq233829 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0))) := by
    intro X0
    first
    | exact superpose eq230758 eq233628
    | exact resolve eq233628 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233628
  have eq240472 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4785 X0 X1 X2 X3
       have i₂ := eq21041 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq21041 eq4785
    | exact resolve eq4785 eq21041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785 eq21041
  have eq241428 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) = (M.op X0 (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq15109 eq240472
    | exact resolve eq240472 eq15109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15109 eq240472
  have eq241855 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op X0 X1))) = (M.op X0 (M.op (σ (M.op x y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq230758 eq241428
    | exact resolve eq241428 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241428
  have eq263839 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)))) := by
    intro X0
    first
    | (have i₁ := eq233829 (M.op (M.op sF1 sF1) x)
       have i₂ := eq128180 sF1 x
       grind)
    | (have i₁ := eq233829 (M.op (M.op X0 X0) sF1)
       have i₂ := eq128180 X0 sF1
       grind)
    | exact superpose eq128180 eq233829
    | exact resolve eq233829 eq128180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128180 eq233829
  have eq264118 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq231205 eq263839
    | exact resolve eq263839 eq231205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263839
  have eq264163 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq264118 X0
       have i₂ := eq91361 X0 sF4
       grind)
    | exact superpose eq91361 eq264118
    | exact resolve eq264118 eq91361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91361 eq264118
  have eq299779 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 X0) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq264163 eq91352
    | exact resolve eq91352 eq264163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91352 eq264163
  have eq411657 : ∀ X0 : G, (M.op (k (σ x) (σ x)) (σ X0)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ (k (k x y) X0)) = (M.op (k (σ x) (σ y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13656 eq456
    | (have j0 := eq456 X0
       grind)
    | exact resolve eq456 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq411658 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ (k (k x y) X0)) = (M.op (k (σ x) (σ y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    grind
  clear eq411657
  have eq411659 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k (k x y) X0)) = (M.op (k (σ x) (σ y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq230758 eq411658
    | (have j0 := eq411658 X0
       grind)
    | exact resolve eq411658 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411658
  have eq411660 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (k (k x y) X0)) = (M.op (k (σ x) (σ y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq231205 eq411659
    | (have j0 := eq411659 X0
       grind)
    | exact resolve eq411659 eq231205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231205 eq411659
  have eq411661 : ∀ X0 : G, (σ (k (k x y) X0)) = (M.op (k (σ x) (σ x)) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13656 eq411660
    | (have j0 := eq411660 X0
       grind)
    | exact resolve eq411660 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411660
  have eq411662 : ∀ X0 : G, (σ (k (k x y) X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    grind
  clear eq411661
  have eq411663 : ∀ X0 : G, (σ (k (k x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq230758 eq411662
    | (have j0 := eq411662 X0
       grind)
    | exact resolve eq411662 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411662
  have eq411664 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ X0)) = (σ (k (k x x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq411663 X0
       have i₂ := eq13447
       grind)
    | exact superpose eq13447 eq411663
    | (have j0 := eq411663 X0
       grind)
    | exact resolve eq411663 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13447 eq411663
  have eq411665 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (k (σ x) (σ y)) := by
    intro X0
    grind
  clear eq411664
  have eq411666 : ∀ X0 : G, (σ X0) = (k (σ x) (σ x)) ∨ (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq13656 eq411665
    | (have j0 := eq411665 X0
       grind)
    | exact resolve eq411665 eq13656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13656 eq411665
  have eq411667 : ∀ X0 : G, (σ X0) = (σ x) ∨ (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    grind
  clear eq411666
  have eq411668 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq230758 eq411667
    | (have j0 := eq411667 X0
       grind)
    | exact resolve eq411667 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411667
  have eq411675 : ∀ X0 : G, (σ (k x (τ X0))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq411668 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq411668
    | exact resolve eq411668 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411668
  have eq412184 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq411675 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq411675
    | (have j0 := eq411675 X0
       grind)
    | exact resolve eq411675 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq411675
  have eq412309 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq230758 eq412184
    | (have j0 := eq412184 X0
       grind)
    | exact resolve eq412184 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412184
  have eq483050 : ∀ X0 X2 X3 : G, (M.op X0 x) = (M.op (M.op X2 (M.op x X3)) (M.op x (M.op X0 x))) := by
    intro X0 X2 X3
    first
    | exact superpose eq230312 eq164252
    | exact resolve eq164252 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164252
  have eq543248 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op x (M.op x x)) X0) ∨ (M.op x (M.op x x)) = X0 ∨ (M.op X0 X0) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op x (M.op x x)) X0
       have i₂ := eq483050 x x x
       grind)
    | exact superpose eq483050 eq12
    | (have j0 := eq12 (M.op x (M.op x x)) X0
       grind)
    | exact resolve eq12 eq483050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483050
  have eq543486 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) ∨ (M.op x (M.op x x)) = X0 ∨ (M.op X0 X0) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq543248 X0
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq543248
    | (have j0 := eq543248 X0
       grind)
    | exact resolve eq543248 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543248
  have eq543583 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op x (M.op x x)) = X0 ∨ (M.op X0 X0) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq543486 X0
       have i₂ := eq13557
       grind)
    | exact superpose eq13557 eq543486
    | (have j0 := eq543486 X0
       grind)
    | (have r₁ := eq543486 y
       have r₂ := eq13557
       grind)
    | exact resolve eq543486 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13557 eq543486
  have eq543628 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x (M.op x x)) = X0 ∨ (M.op X0 X0) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | exact superpose eq230312 eq543583
    | (have j0 := eq543583 X0
       grind)
    | exact resolve eq543583 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543583
  have eq543640 : ∀ X0 : G, x = X0 ∨ x ≠ (M.op x X0) ∨ (M.op X0 X0) = (k (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq543628 X0
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq543628
    | (have j0 := eq543628 X0
       grind)
    | (have r₁ := eq543628 (M.op x x)
       have r₂ := eq54 x
       grind)
    | exact resolve eq543628 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543628
  have eq543649 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = X0 ∨ (M.op X0 X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq543640 X0
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq543640
    | (have j0 := eq543640 X0
       grind)
    | (have r₁ := eq543640 (M.op x x)
       have r₂ := eq54 x
       grind)
    | exact resolve eq543640 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543640
  have eq592583 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op X1 X0)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq230758 eq43858
    | exact resolve eq43858 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43858
  have eq728957 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op X0 X1)) = (M.op X1 (M.op X0 (M.op (σ (M.op x y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq241855 eq592583
    | exact resolve eq592583 eq241855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241855 eq592583
  have eq1336800 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) = (k (σ x) (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1)))) ∨ (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq13683 eq9245
    | (have j0 := eq9245 X0 X1
       grind)
    | exact resolve eq9245 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9245
  have eq1336801 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) = (k (σ x) (M.op (M.op (M.op (σ x) (σ x)) X1) (M.op X0 (M.op (M.op (σ x) (σ x)) X1)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1336800 X0 X1
       have i₂ := eq129385 X0 (M.op (M.op sF2 sF2) X1) X0
       grind)
    | exact superpose eq129385 eq1336800
    | (have j0 := eq1336800 X0 X1
       grind)
    | exact resolve eq1336800 eq129385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336800
  have eq1336802 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (k (σ x) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq13683 eq1336801
    | (have j0 := eq1336801 X0 X1
       grind)
    | exact resolve eq1336801 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336801
  have eq1336803 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (k (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (M.op X0 (M.op (M.op (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq230758 eq1336802
    | (have j0 := eq1336802 X0 X1
       grind)
    | exact resolve eq1336802 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336802
  have eq1336804 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X1) (M.op X0 (M.op (M.op (σ x) (σ x)) X1))) ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (k (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1336803 X0 X1
       have i₂ := eq129385 X0 (M.op (M.op sF2 sF2) X1) X0
       grind)
    | exact superpose eq129385 eq1336803
    | (have j0 := eq1336803 X0 X1
       grind)
    | exact resolve eq1336803 eq129385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129385 eq1336803
  have eq1336805 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1))) ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (k (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq13683 eq1336804
    | (have j0 := eq1336804 X0 X1
       grind)
    | exact resolve eq1336804 eq13683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13683 eq1336804
  have eq1336806 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (k (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X0 (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq230758 eq1336805
    | (have j0 := eq1336805 X0 X1
       grind)
    | exact resolve eq1336805 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336805
  have eq1336931 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)))) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq728957 eq1336806
    | (have j0 := eq1336806 (σ (M.op x y)) X0
       grind)
    | exact resolve eq1336806 eq728957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728957 eq1336806
  have eq1337175 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (σ (M.op x y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)))) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq1336931 X0
       have i₂ := eq159050 sF1 (M.op sF4 X0) sF4 sF1
       grind)
    | exact superpose eq159050 eq1336931
    | (have j0 := eq1336931 X0
       grind)
    | exact resolve eq1336931 eq159050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336931
  have eq1337291 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq299779 eq1337175
    | (have j0 := eq1337175 X0
       grind)
    | exact resolve eq1337175 eq299779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337175
  have eq1337395 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) ∨ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq1337291 X0
       have i₂ := eq159050 sF1 (M.op sF4 X0) sF4 sF1
       grind)
    | exact superpose eq159050 eq1337291
    | (have j0 := eq1337291 X0
       grind)
    | exact resolve eq1337291 eq159050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159050 eq1337291
  have eq1337494 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq299779 eq1337395
    | (have j0 := eq1337395 X0
       grind)
    | exact resolve eq1337395 eq299779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299779 eq1337395
  have eq1337576 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) = (k (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq1337494 X0
       have j1 := eq412309 (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | (have r₁ := eq1337494 X0
       have r₂ := eq412309 (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | exact resolve eq1337494 eq412309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412309 eq1337494
  have eq2190634 : (k (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1337576 (M.op sF4 sF4)
       have i₂ := eq54 sF4
       grind)
    | exact superpose eq54 eq1337576
    | exact resolve eq1337576 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1337576
  have eq2190777 : (k (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2190634
       have r₂ := eq28
       grind)
    | exact resolve eq2190634 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190634
  have eq2190836 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq233361 eq2190777
    | exact resolve eq2190777 eq233361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233361 eq2190777
  have eq2811626 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ (M.op x y) = (M.op x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq230758 eq141984
    | (have j0 := eq141984 X0
       grind)
    | exact resolve eq141984 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141984
  have eq2811627 : ∀ X0 : G, (M.op x (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq230312 eq2811626
    | (have j0 := eq2811626 X0
       grind)
    | exact resolve eq2811626 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811626
  have eq3049831 : ∀ X0 : G, x ≠ (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x (τ X0)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq2811627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811627
  have eq3050648 : x ≠ (τ (σ (M.op x y))) ∨ x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2190836 eq3049831
    | (have j0 := eq3049831 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3049831 eq2190836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049831
  have eq3050708 : x ≠ (M.op x y) ∨ x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31 eq3050648
    | exact resolve eq3050648 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3050648
  have eq3050731 : x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3050708
       have r₂ := eq230312
       grind)
    | exact resolve eq3050708 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3050708
  have eq3050849 : x ≠ x ∨ x = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3050731 eq543649
    | (have j0 := eq543649 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq543649 (τ (M.op (σ x) (σ y)))
       have r₂ := eq3050731
       grind)
    | exact resolve eq543649 eq3050731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543649 eq3050731
  have eq3051191 : x ≠ x ∨ x = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k x (τ (M.op (σ x) (σ y)))) := by grind
  clear eq3050849
  have eq3051192 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k x (τ (M.op (σ x) (σ y)))) := by grind
  clear eq3051191
  have eq3051330 : (τ (k (σ x) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3051192
       have i₂ := eq202 sF4
       grind)
    | exact superpose eq202 eq3051192
    | exact resolve eq3051192 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq3051192
  have eq3051430 : (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230758 eq3051330
    | exact resolve eq3051330 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051330
  have eq3051497 : (τ (σ (M.op x y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2190836 eq3051430
    | exact resolve eq3051430 eq2190836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190836 eq3051430
  have eq3051538 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31 eq3051497
    | exact resolve eq3051497 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3051497
  have eq3051559 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230312 eq3051538
    | exact resolve eq3051538 eq230312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230312 eq3051538
  have eq3060723 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x (τ (M.op (σ x) (σ y))))) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3051559 eq19185
    | exact resolve eq19185 eq3051559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19185 eq3051559
  have eq3061247 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3060723 x
       have i₂ := eq230537 x (τ sF4)
       grind)
    | exact superpose eq230537 eq3060723
    | exact resolve eq3060723 eq230537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230537 eq3060723
  have eq3061248 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq3061247
  have eq3061381 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3061248 eq15
    | exact resolve eq15 eq3061248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061248
  have eq3061938 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3061381
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3061381
    | exact resolve eq3061381 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3061381
  have eq3062015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq230758 eq3061938
    | exact resolve eq3061938 eq230758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230758 eq3061938
  have eq3062047 : False := by grind
  exact eq3062047

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq181 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq26
    | exact resolve eq26 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193 y x
       grind)
    | exact superpose eq193 eq16
    | (have j1 := eq193 y x
       grind)
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq259 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ (M.op X0 X0))
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq9
    | exact resolve eq9 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq260 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq259
    | exact resolve eq259 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq259
  have eq299 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq260 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq260
    | exact resolve eq260 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq306 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq299
    | exact resolve eq299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq310 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq306
    | exact resolve eq306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq368 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op X0 X0)
       have i₂ := eq310 X0 X0
       grind)
    | exact superpose eq310 eq26
    | exact resolve eq26 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq310
  have eq479 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq368 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq368
    | exact resolve eq368 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq202
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq202
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq202
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq202
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq202 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq929 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq928
  have eq22257 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq929
       grind)
    | exact superpose eq929 eq16
    | exact resolve eq16 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq22258 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq22257
       have r₂ := eq23 x
       grind)
    | exact resolve eq22257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22257
  have eq143797 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22258
       grind)
    | exact superpose eq22258 eq10
    | exact resolve eq10 eq22258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22258
  have eq143932 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq143797
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq143797
    | exact resolve eq143797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143797
  have eq143934 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq143932
       grind)
    | exact superpose eq143932 eq16
    | exact resolve eq16 eq143932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143932
  have eq143935 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq143934
       have r₂ := eq23 x
       grind)
    | exact resolve eq143934 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq143934
  have eq144977 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq143935
       grind)
    | exact superpose eq143935 eq10
    | exact resolve eq10 eq143935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143935
  have eq145162 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq144977
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq144977
    | exact resolve eq144977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144977
  have eq145163 : x = (M.op y y) := by grind
  clear eq145162
  have eq145239 : x = (M.op x y) := by
    first
    | (have i₁ := eq368 y
       have i₂ := eq145163
       grind)
    | exact superpose eq145163 eq368
    | exact resolve eq368 eq145163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq145241 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq479 y
       have i₂ := eq145163
       grind)
    | exact superpose eq145163 eq479
    | exact resolve eq479 eq145163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq145163
  have eq173095 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145241
       grind)
    | exact superpose eq145241 eq16
    | exact resolve eq16 eq145241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145241
  have eq173361 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq173095
       have i₂ := eq145239
       grind)
    | exact superpose eq145239 eq173095
    | exact resolve eq173095 eq145239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145239 eq173095
  have eq173362 : False := by grind
  exact eq173362

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq255 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq289 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq278
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq290 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq289
  have eq404 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq56
    | exact resolve eq56 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq625 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq16
    | exact resolve eq16 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq708 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq758 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq404 (M.op X0 X0)
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq404
    | exact resolve eq404 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq919 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq255 (τ X0)
       have i₂ := eq625 X0
       grind)
    | exact superpose eq625 eq255
    | exact resolve eq255 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq625
  have eq4251 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X0 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq708
    | exact resolve eq708 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq708
  have eq4305 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4251 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4251
    | (have j0 := eq4251 y x
       grind)
    | exact resolve eq4251 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq14922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq14921
    | exact resolve eq14921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14921
  have eq14933 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq14922
       have r₂ := eq28
       grind)
    | exact resolve eq14922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14922
  have eq14957 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14933 eq4251
    | exact resolve eq4251 eq14933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15157 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14957 eq14933
    | exact resolve eq14933 eq14957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14933 eq14957
  have eq15179 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq15157
  have eq15213 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq15179 eq919
    | exact resolve eq919 eq15179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq15179
  have eq15238 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq15213
    | exact resolve eq15213 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15213
  have eq15252 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq15238
    | exact resolve eq15238 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15238
  have eq15253 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15252
  have eq15399 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4251 x y
       have i₂ := eq15253
       grind)
    | exact superpose eq15253 eq4251
    | exact resolve eq4251 eq15253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4251
  have eq15623 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15253
       have i₂ := eq15399
       grind)
    | exact superpose eq15399 eq15253
    | exact resolve eq15253 eq15399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15253 eq15399
  have eq15645 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15623
  have eq15664 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq56
    | exact resolve eq56 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq15645
  have eq15709 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq15664
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15664
    | exact resolve eq15664 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15736 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15709 eq30
    | exact resolve eq30 eq15709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15709
  have eq15855 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq15736
    | exact resolve eq15736 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15736
  have eq15856 : x = (M.op x y) ∨ x = y := by grind
  clear eq15855
  have eq16001 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15856 eq21
    | exact resolve eq21 eq15856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16062 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15856 eq4305
    | exact resolve eq4305 eq15856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305 eq15856
  have eq16074 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16062
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16062
    | exact resolve eq16062 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16062
  have eq16125 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16001
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16001
    | exact resolve eq16001 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16001
  have eq16140 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq16125 eq27
    | exact resolve eq27 eq16125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16125
  have eq16307 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq758 y
       have i₂ := eq16074
       grind)
    | exact superpose eq16074 eq758
    | exact resolve eq758 eq16074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq16074
  have eq16332 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq16307
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16307
    | exact resolve eq16307 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16307
  have eq16350 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq16332
    | exact resolve eq16332 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16332
  have eq16948 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq16350 eq16140
    | exact resolve eq16140 eq16350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16140 eq16350
  have eq16968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq16948
  have eq16971 : x = y := by
    first
    | (have r₁ := eq16968
       have r₂ := eq28
       grind)
    | exact resolve eq16968 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16968
  have eq16973 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16971
       grind)
    | exact superpose eq16971 eq19
    | exact resolve eq19 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16974 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16971
       grind)
    | exact superpose eq16971 eq25
    | exact resolve eq25 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16971
  have eq17083 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16974
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16974
    | exact resolve eq16974 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16974
  have eq17099 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17083 eq27
    | exact resolve eq27 eq17083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17083
  have eq17361 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17099 eq77
    | exact resolve eq77 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq17099
  have eq17424 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17361
       have i₂ := eq16973
       grind)
    | exact superpose eq16973 eq17361
    | exact resolve eq17361 eq16973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16973 eq17361
  have eq17434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17424 eq15
    | exact resolve eq15 eq17424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17424
  have eq17483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17434
    | exact resolve eq17434 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17434
  have eq17492 : False := by grind
  exact eq17492

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X0) X0 X1 X2
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq470 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X0 X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq65
    | exact resolve eq65 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq777 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq31 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq31 eq61
    | exact resolve eq61 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1253 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1224
  have eq1610 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1253
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1253
       grind)
    | exact resolve eq13 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1626 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq470 (σ y) (σ x)
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq470
    | exact resolve eq470 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1627 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1610
  have eq1628 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1627
  have eq1630 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1626
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq1626
    | exact resolve eq1626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1635 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1628
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1628
    | exact resolve eq1628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq3197 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1635
       grind)
    | exact superpose eq1635 eq10
    | exact resolve eq10 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq3232 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3197
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3197
    | exact resolve eq3197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3234 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq3232
       have r₂ := eq13 x y
       grind)
    | exact resolve eq3232 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq5659 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq3234
       grind)
    | exact superpose eq3234 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq3234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3234
  have eq5660 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5659
  have eq8516 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq5660
       grind)
    | exact superpose eq5660 eq9
    | exact resolve eq9 eq5660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14886 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8516 x
       have i₂ := eq5660
       grind)
    | exact superpose eq5660 eq8516
    | exact resolve eq8516 eq5660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660 eq8516
  have eq14955 : x = (M.op y (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14886
  have eq26558 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 (M.op x x)
       have i₂ := eq14955
       grind)
    | exact superpose eq14955 eq9
    | exact resolve eq9 eq14955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14955
  have eq58567 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq777 x (M.op y y)
       have i₂ := eq26558 x
       grind)
    | exact superpose eq26558 eq777
    | exact resolve eq777 eq26558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq26558
  have eq68089 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31 y X0
       have i₂ := eq58567
       grind)
    | exact superpose eq58567 eq31
    | exact resolve eq31 eq58567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58567
  have eq168795 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op x y) x
       have i₂ := eq68089 x
       grind)
    | exact superpose eq68089 eq56
    | exact resolve eq56 eq68089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68089
  have eq168999 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq168795 x
       have i₂ := eq470 (σ y) x
       grind)
    | exact superpose eq470 eq168795
    | exact resolve eq168795 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168795
  have eq169055 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq168999
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq168999
    | exact resolve eq168999 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168999
  have eq253842 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1630
       grind)
    | exact superpose eq1630 eq16
    | exact resolve eq16 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq254216 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq253842
       have r₂ := eq169055
       grind)
    | exact resolve eq253842 eq169055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169055 eq253842
  have eq257636 : y = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq254216
       grind)
    | exact superpose eq254216 eq31
    | exact resolve eq31 eq254216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq257654 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq470 y x
       have i₂ := eq254216
       grind)
    | exact superpose eq254216 eq470
    | exact resolve eq470 eq254216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268908 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq257636
       have i₂ := eq257654
       grind)
    | exact superpose eq257654 eq257636
    | exact resolve eq257636 eq257654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257636
  have eq269064 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq268908
  have eq350162 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq269064
       have i₂ := eq254216
       grind)
    | exact superpose eq254216 eq269064
    | exact resolve eq269064 eq254216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254216 eq269064
  have eq350375 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq350162
  have eq378339 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq56 x x
       have i₂ := eq350375
       grind)
    | exact superpose eq350375 eq56
    | exact resolve eq56 eq350375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq378340 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq350375
       grind)
    | exact superpose eq350375 eq57
    | exact resolve eq57 eq350375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq350375
  have eq378732 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378339 x
       have i₂ := eq470 (σ y) x
       grind)
    | exact superpose eq470 eq378339
    | exact resolve eq378339 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq378339
  have eq378797 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378732
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq378732
    | exact resolve eq378732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378732
  have eq597775 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378797
       have i₂ := eq257654
       grind)
    | exact superpose eq257654 eq378797
    | exact resolve eq378797 eq257654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257654 eq378797
  have eq598300 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq597775
  have eq793730 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq378340
       grind)
    | exact superpose eq378340 eq16
    | exact resolve eq16 eq378340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378340
  have eq794244 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq793730
       have r₂ := eq598300
       grind)
    | exact resolve eq793730 eq598300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598300 eq793730
  have eq828314 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq794244
       grind)
    | exact superpose eq794244 eq10
    | exact resolve eq10 eq794244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794244
  have eq828889 : x = y ∨ x = y := by
    first
    | (have i₁ := eq828314
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq828314
    | exact resolve eq828314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828314
  have eq828890 : x = y := by grind
  clear eq828889
  have eq858903 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq828890
       grind)
    | exact superpose eq828890 eq16
    | exact resolve eq16 eq828890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828890
  have eq858904 : False := by grind
  exact eq858904

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (σ (k X2 (k X1 (τ X0)))) = (k (σ X2) (k (σ X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 (M.op X1 X0) (M.op X1 X1) X2
       have i₂ := eq9 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X0) X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq73
    | exact resolve eq73 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq366 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq71 X0 X1 X0
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X2 (M.op X0 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X3
       have i₂ := eq62 X0 X0 X2 X1
       grind)
    | exact superpose eq62 eq73
    | exact resolve eq73 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq443 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq416 X2 X1 (M.op X2 X1) (M.op x X1)
       have i₂ := eq71 X1 X2 x
       grind)
    | exact superpose eq71 eq416
    | exact resolve eq416 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq469 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X2 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443 (M.op X1 X1) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq443
    | exact resolve eq443 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq443
    | exact resolve eq443 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443 (M.op (M.op X2 X1) (M.op X2 X1)) (M.op X0 X1)
       have i₂ := eq71 X1 X2 X0
       grind)
    | exact superpose eq71 eq443
    | exact resolve eq443 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = (M.op (M.op X1 X0) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469 X0 X1 X2
       have i₂ := eq470 (M.op X1 X0) X2
       grind)
    | exact superpose eq470 eq469
    | exact resolve eq469 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq535 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 X2
       have i₂ := eq470 X0 X1
       grind)
    | exact superpose eq470 eq71
    | exact resolve eq71 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq536 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 X0) (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X0 X3 X2 X1
       have i₂ := eq470 (M.op X0 X1) X2
       grind)
    | exact superpose eq470 eq62
    | exact resolve eq62 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq549 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X1 X0)
       have i₂ := eq470 X0 X1
       grind)
    | exact superpose eq470 eq63
    | exact resolve eq63 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq490 X0 X1 X0
       grind)
    | exact superpose eq490 eq549
    | exact resolve eq549 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq559 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X3 X0) (M.op X0 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq536 X0 X1 X2 X3
       have i₂ := eq490 X1 X0 X2
       grind)
    | exact superpose eq490 eq536
    | exact resolve eq536 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq645 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X3 X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X2 X1 X3
       have i₂ := eq83 X2 X1 X0
       grind)
    | (have i₁ := eq83 X0 X0 X2
       have i₂ := eq83 X0 X0 X0
       grind)
    | exact superpose eq83 eq83
    | exact resolve eq83 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X1 (M.op X0 X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq83
    | exact resolve eq83 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 X1 X2
       have i₂ := eq83 X1 X2 X0
       grind)
    | (have i₁ := eq470 X0 X0
       have i₂ := eq83 X0 X0 X0
       grind)
    | exact superpose eq83 eq470
    | exact resolve eq470 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq470 X1 (M.op X0 X0)
       grind)
    | exact superpose eq470 eq658
    | exact resolve eq658 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq730 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X3 (M.op X0 (M.op X2 X1))) (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq676 X0 X0 (M.op X2 (M.op X1 X0))
       have i₂ := eq366 X0 X1 X2
       grind)
    | exact superpose eq366 eq676
    | exact resolve eq676 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq735 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 (M.op X0 X2))) = (M.op (M.op X3 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq676 X0 (M.op X2 X1) X1
       have i₂ := eq676 X0 X1 X2
       grind)
    | (have i₁ := eq676 X0 (M.op X2 X1) (M.op X0 X2)
       have i₂ := eq676 X0 X1 X2
       grind)
    | exact superpose eq676 eq676
    | exact resolve eq676 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X3 X2) (M.op (M.op X1 X0) (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq535 X2 X0 X3
       have i₂ := eq676 X1 X2 X0
       grind)
    | (have i₁ := eq535 (M.op X0 X2) X2 X2
       have i₂ := eq676 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq676 eq535
    | exact resolve eq535 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X3 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq735 X0 X1 X2 X3
       have i₂ := eq535 X2 X0 X0
       grind)
    | exact superpose eq535 eq735
    | exact resolve eq735 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq735
  have eq801 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X2 X1))) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq730 X0 X1 X2 X3
       have i₂ := eq63 X1
       grind)
    | (have i₁ := eq730 X0 X1 X2 X3
       have i₂ := eq63 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq63 eq730
    | exact resolve eq730 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq998 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op X4 (M.op X3 (M.op X1 (M.op X0 X2)))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq83 (M.op X1 X1) (M.op X3 (M.op X0 (M.op X2 X1))) X2
       have i₂ := eq801 X0 X1 X2 X3
       grind)
    | exact superpose eq801 eq83
    | exact resolve eq83 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1247 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X1 X2) (M.op X2 X0))) = (M.op (M.op X2 X0) (M.op (M.op X1 X2) (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq676 X0 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq645 X0 X1 X2 X3
       grind)
    | (have i₁ := eq676 X0 (M.op X1 X2) (M.op X3 X1)
       have i₂ := eq645 X0 X1 X2 X3
       grind)
    | exact superpose eq645 eq676
    | exact resolve eq676 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1252 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X1 X2) (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1247 X0 X1 X2 X3 X4
       have i₂ := eq746 X2 X1 X0 X2
       grind)
    | exact superpose eq746 eq1247
    | exact resolve eq1247 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq1247
  have eq1391 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq129 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq129 X0 X1
       grind)
    | exact resolve eq13 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1412 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq1413 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1421 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1413
    | (have j0 := eq1413 X0 X1
       grind)
    | exact resolve eq1413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1428 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 X1 X0 X2
       have i₂ := eq470 X0 X1
       grind)
    | exact superpose eq470 eq471
    | exact resolve eq471 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq471
  have eq2649 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 (M.op X3 (M.op X1 (M.op X0 X2))))) (M.op (M.op X2 X2) X2)) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq796 (M.op X3 (M.op X0 (M.op X2 X1))) X1 (M.op X1 X1) X3
       have i₂ := eq801 X0 X1 X2 X3
       grind)
    | exact superpose eq801 eq796
    | exact resolve eq796 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq2730 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 (M.op X3 (M.op X1 (M.op X0 X2))))) (M.op X2 X2)) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2649 X0 X1 X2 X3 X4 X5
       have i₂ := eq84 X2 X2
       grind)
    | exact superpose eq84 eq2649
    | exact resolve eq2649 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq3261 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op X5 (M.op X6 (M.op X0 (M.op X2 (M.op X4 (M.op X1 X3)))))) (M.op X3 (M.op X3 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq796 (M.op X4 (M.op X3 (M.op X1 (M.op X0 X2)))) X1 X2 X3
       have i₂ := eq998 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq998 eq796
    | exact resolve eq796 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq998
  have eq3291 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op X5 (M.op X6 (M.op X0 (M.op X2 (M.op X4 (M.op X1 X3)))))) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3261 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq63 X3
       grind)
    | (have i₁ := eq3261 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq63 (M.op X3 (M.op X3 X3))
       grind)
    | exact superpose eq63 eq3261
    | exact resolve eq3261 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq3261
  have eq6054 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 X0) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq676 X3 (M.op X2 X1) X0
       have i₂ := eq490 X1 X2 X0
       grind)
    | exact superpose eq490 eq676
    | exact resolve eq676 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq676
  have eq9559 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op X4 X2) (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq559 X2 X3 X0 X4
       have i₂ := eq6054 X0 X3 X2 X1
       grind)
    | (have i₁ := eq559 (M.op X3 X0) X1 X0 X3
       have i₂ := eq6054 X0 X1 (M.op X3 X0) X3
       grind)
    | exact superpose eq6054 eq559
    | exact resolve eq559 eq6054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq6054
  have eq12419 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op X6 (M.op X7 (M.op X1 (M.op X0 (M.op X3 (M.op X5 (M.op X2 X4))))))) (M.op (M.op X8 (M.op X1 (M.op X0 (M.op X3 (M.op X5 (M.op X2 X4)))))) X4)) = X4 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq1252 (M.op X2 X2) X1 (M.op X4 (M.op X5 (M.op X3 (M.op X1 (M.op X0 X2))))) X3 X4
       have i₂ := eq2730 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq2730 eq1252
    | exact resolve eq1252 eq2730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq2730
  have eq12469 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X6 (M.op X7 (M.op X1 (M.op X0 (M.op X3 (M.op X5 (M.op X2 X4))))))) (M.op X4 X4)) = X4 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq12419 X0 X1 X2 X3 X4 X5 X6 X7 x
       have i₂ := eq3291 X0 X2 X3 X4 X5 x X1
       grind)
    | exact superpose eq3291 eq12419
    | exact resolve eq12419 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291 eq12419
  have eq19906 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1421 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq1421
    | (have j0 := eq1421 (τ X0) (τ X1)
       grind)
    | exact resolve eq1421 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq20183 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X1 X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19906 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19906
    | (have j0 := eq19906 X0 X1
       grind)
    | exact resolve eq19906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19906
  have eq20187 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20183 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq20183
    | (have j0 := eq20183 X0 X1
       grind)
    | exact resolve eq20183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20183
  have eq20190 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20187 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20187
    | (have j0 := eq20187 X0 X1
       grind)
    | exact resolve eq20187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20187
  have eq20191 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X1 X0))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20190 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20190
    | (have j0 := eq20190 X0 X1
       grind)
    | exact resolve eq20190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20190
  have eq20192 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20191 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq20191
    | (have j0 := eq20191 X0 X1
       grind)
    | exact resolve eq20191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq20193 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20192 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20192
    | (have j0 := eq20192 X0 X1
       grind)
    | exact resolve eq20192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192
  have eq20194 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20193 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20193
    | (have j0 := eq20193 X0 X1
       grind)
    | exact resolve eq20193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20193
  have eq20366 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20194 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20367 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq20194 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20194
  have eq20521 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20366 (M.op X0 X1) X0
       have i₂ := eq443 X1 X0
       grind)
    | exact superpose eq443 eq20366
    | (have j0 := eq20366 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq20366 (M.op x X1) x
       have r₂ := eq443 X1 x
       grind)
    | exact resolve eq20366 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20366
  have eq20547 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20521
  have eq20690 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20547 (M.op x X1) x
       have i₂ := eq443 X1 x
       grind)
    | exact superpose eq443 eq20547
    | exact resolve eq20547 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20769 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op (σ X0) X1) X0
       have i₂ := eq20547 (σ X0) X1
       grind)
    | exact superpose eq20547 eq25
    | (have j1 := eq20547 (σ X0) X1
       grind)
    | exact resolve eq25 eq20547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20547
  have eq20827 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20690 X0 X1
       have i₂ := eq1428 X1 X0 X0
       grind)
    | exact superpose eq1428 eq20690
    | (have j0 := eq20690 X0 X1
       grind)
    | exact resolve eq20690 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq20690
  have eq64785 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) X1)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20827 (M.op X0 X0) X1
       have i₂ := eq705 X0 X1
       grind)
    | (have i₁ := eq20827 (M.op X1 X1) X1
       have i₂ := eq705 X1 X1
       grind)
    | exact superpose eq705 eq20827
    | (have j0 := eq20827 (M.op X0 X0) X1
       grind)
    | exact resolve eq20827 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq20827
  have eq65034 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k X0 (M.op (M.op X0 X0) X1)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64785 X0 X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq64785
    | (have j0 := eq64785 X0 X1
       grind)
    | exact resolve eq64785 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64785
  have eq65041 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (k X0 (M.op (M.op X0 X0) X1)) ∨ (M.op (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65034 X0 X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq65034
    | (have j0 := eq65034 X0 X1
       grind)
    | exact resolve eq65034 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq65034
  have eq112579 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X1)) (τ X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20769 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20769
    | exact resolve eq20769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20769
  have eq112794 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X1) X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112579 X0 X1
       have i₂ := eq35 X0 (M.op X0 X1)
       grind)
    | exact superpose eq35 eq112579
    | (have j0 := eq112579 X0 X1
       grind)
    | exact resolve eq112579 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112579
  have eq113275 : ∀ X0 X1 X2 : G, (τ (k (k (M.op X0 X1) X0) X2)) = (k (τ (M.op X0 X0)) (τ X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X2 (k (M.op X0 X1) X0)
       have i₂ := eq112794 X0 X1
       grind)
    | exact superpose eq112794 eq35
    | (have j1 := eq112794 X0 X1
       grind)
    | exact resolve eq35 eq112794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112794
  have eq113397 : ∀ X0 X1 X2 : G, (τ (k (M.op X0 X0) X2)) = (τ (k (k (M.op X0 X1) X0) X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113275 X0 X1 X2
       have i₂ := eq35 X2 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq113275
    | (have j0 := eq113275 X0 X1 X2
       grind)
    | exact resolve eq113275 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113275
  have eq113824 : ∀ X0 X1 X2 : G, (σ (τ (k (M.op X1 X1) X0))) = (k (k (M.op X1 X2) X1) X0) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (k (M.op X1 X2) X1) X0)
       have i₂ := eq113397 X1 X2 X0
       grind)
    | exact superpose eq113397 eq11
    | (have j1 := eq113397 X1 X2 X2
       grind)
    | exact resolve eq11 eq113397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113397
  have eq113957 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) X0) = (k (k (M.op X1 X2) X1) X0) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113824 X0 X1 X2
       have i₂ := eq11 (k (M.op X1 X1) X0)
       grind)
    | exact superpose eq11 eq113824
    | (have j0 := eq113824 X0 X1 X2
       grind)
    | exact resolve eq113824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113824
  have eq326238 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k X0 (M.op X1 (M.op X0 X2))) ∨ (M.op X1 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65041 X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 x)))
       have i₂ := eq9559 X0 X1 X2 x X2
       grind)
    | exact superpose eq9559 eq65041
    | exact resolve eq65041 eq9559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9559 eq65041
  have eq370818 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq326238 X0 X1 (M.op X1 X0)
       have i₂ := eq554 X0 X1
       grind)
    | exact superpose eq554 eq326238
    | exact resolve eq326238 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq326238
  have eq371528 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq370818 (σ X0) (σ X1)
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq370818
    | (have j1 := eq129 X0 X1
       grind)
    | exact resolve eq370818 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq370818
  have eq371974 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq371528 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371528
  have eq372027 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq371974 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371974
    | (have j0 := eq371974 X0 X1
       grind)
    | exact resolve eq371974 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371974
  have eq372028 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq372027 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372027
  have eq372212 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372028 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372028
    | exact resolve eq372028 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372271 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq372028 x y
       grind)
    | exact superpose eq372028 eq16
    | (have j1 := eq372028 x y
       grind)
    | exact resolve eq16 eq372028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372285 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X1) (σ X0)
       have i₂ := eq372028 X0 X1
       grind)
    | exact superpose eq372028 eq84
    | (have j1 := eq372028 X0 X1
       grind)
    | exact resolve eq84 eq372028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq372028
  have eq372710 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372212 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq372212
    | (have j0 := eq372212 X0 X1
       grind)
    | exact resolve eq372212 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372212
  have eq372738 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq372710 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372710
    | exact resolve eq372710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372855 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq372710 X0 X1
       grind)
    | exact superpose eq372710 eq32
    | (have j1 := eq372710 X0 X1
       grind)
    | exact resolve eq32 eq372710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372710
  have eq374865 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq372271
       have i₂ := eq372738 x y
       grind)
    | exact superpose eq372738 eq372271
    | (have j1 := eq372738 (σ x) (σ y)
       grind)
    | (have r₁ := eq372271
       have r₂ := eq372738 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq372271
       have r₂ := eq372738 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq372271 eq372738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372271 eq372738
  have eq374871 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq374865
  have eq374874 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq374871
       grind)
    | exact superpose eq374871 eq10
    | exact resolve eq10 eq374871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374871
  have eq374972 : x = y ∨ x = y := by
    first
    | (have i₁ := eq374874
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq374874
    | exact resolve eq374874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374874
  have eq374973 : x = y := by grind
  clear eq374972
  have eq374974 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq374973
       grind)
    | exact superpose eq374973 eq16
    | exact resolve eq16 eq374973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374973
  have eq375409 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq372855 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372855
    | exact resolve eq372855 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372855
  have eq375723 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq375409 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq375409
    | (have j0 := eq375409 (τ (k X0 X1)) (τ (M.op X0 X1))
       grind)
    | exact resolve eq375409 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375409
  have eq376644 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 X1))) = (k (τ X2) (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (k X0 X1) X2
       have i₂ := eq375723 X0 X1
       grind)
    | exact superpose eq375723 eq35
    | (have j1 := eq375723 (τ (k X2 (k X0 X1))) (k (τ X2) (τ (M.op X0 X1)))
       grind)
    | exact resolve eq35 eq375723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375723
  have eq376850 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 X1))) = (τ (k X2 (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376644 X0 X1 X2
       have i₂ := eq35 (M.op X0 X1) X2
       grind)
    | exact superpose eq35 eq376644
    | (have j0 := eq376644 (τ (k X2 (k X0 X1))) (τ (k X2 (M.op X0 X1))) X2
       grind)
    | exact resolve eq376644 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376644
  have eq381880 : ∀ X0 X1 X2 : G, (τ (σ (k X0 (k X2 (τ X1))))) = (τ (k (σ X0) (M.op (σ X2) X1))) ∨ (σ X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376850 (σ X2) X1 (σ X0)
       have i₂ := eq30 X1 X2 X0
       grind)
    | exact superpose eq30 eq376850
    | (have j0 := eq376850 (τ (σ (k X0 (k X2 (τ X1))))) (τ (k (σ X0) (M.op (σ X2) X1))) X2
       grind)
    | exact resolve eq376850 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq376850
  have eq382277 : ∀ X0 X1 X2 : G, (τ (σ (k X0 (k X2 (τ X1))))) = (k X0 (τ (M.op (σ X2) X1))) ∨ (σ X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq381880 X0 X1 X2
       have i₂ := eq32 (M.op (σ X2) X1) X0
       grind)
    | exact superpose eq32 eq381880
    | (have j0 := eq381880 X0 X1 X2
       grind)
    | exact resolve eq381880 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq381880
  have eq382358 : ∀ X0 X1 X2 : G, (k X0 (k X2 (τ X1))) = (k X0 (τ (M.op (σ X2) X1))) ∨ (σ X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382277 X0 X1 X2
       have i₂ := eq10 (k X0 (k X2 (τ X1)))
       grind)
    | exact superpose eq10 eq382277
    | (have j0 := eq382277 X0 X1 X2
       grind)
    | exact resolve eq382277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382277
  have eq395952 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ (k X1 X0))) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372285 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq372285
    | (have j0 := eq372285 (τ X0) (τ X1)
       grind)
    | exact resolve eq372285 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372285
  have eq396613 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ (k X1 X0))) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq395952 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395952
    | (have j0 := eq395952 X0 X1
       grind)
    | exact resolve eq395952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395952
  have eq396667 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X1 X0) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq396613 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq396613
    | (have j0 := eq396613 X0 X1
       grind)
    | exact resolve eq396613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396613
  have eq396698 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op (k X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq396667 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq396667
    | (have j0 := eq396667 X0 X1
       grind)
    | exact resolve eq396667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396667
  have eq396721 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X1 X0) X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq396698 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq396698
    | (have j0 := eq396698 X0 X1
       grind)
    | exact resolve eq396698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396698
  have eq397153 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (k X1 X0) X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20367 (k X1 X0) X0
       have i₂ := eq396721 X0 X1
       grind)
    | exact superpose eq396721 eq20367
    | (have j0 := eq20367 X0 X0
       have j1 := eq396721 (M.op X0 X0) (k (k X1 X0) X0)
       grind)
    | (have r₁ := eq20367 (k X1 X0) X0
       have r₂ := eq396721 X0 X1
       grind)
    | (have r₁ := eq20367 X0 X1
       have r₂ := eq396721 (M.op X1 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq20367 X0 X1
       have r₂ := eq396721 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq20367 eq396721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20367 eq396721
  have eq397635 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X1 X0) X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq397153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397153
  have eq406664 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113957 X0 X0 X1
       have i₂ := eq397635 X0 (M.op X0 X1)
       grind)
    | exact superpose eq397635 eq113957
    | (have j0 := eq113957 X0 X0 X1
       have j1 := eq397635 X0 (M.op X0 X1)
       grind)
    | exact resolve eq113957 eq397635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113957
  have eq406961 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq406664 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406664
  have eq475888 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) (k X0 (τ X1))) ∨ (σ X0) = X1 := by
    intro X0 X1
    grind
  clear eq382358
  have eq924726 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) (k (τ X0) (τ X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq475888 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq475888
    | exact resolve eq475888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475888
  have eq925755 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) (τ (k X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq924726 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq924726
    | (have j0 := eq924726 (τ (M.op X0 X1)) (k (τ (M.op X0 X1)) (τ (k X0 X1)))
       grind)
    | exact resolve eq924726 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924726
  have eq925772 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (τ (k (M.op X0 X1) (k X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq925755 X0 X1
       have i₂ := eq35 (k X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq35 eq925755
    | (have j0 := eq925755 (τ (M.op X0 X1)) (τ (k (M.op X0 X1) (k X0 X1)))
       grind)
    | exact resolve eq925755 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq925755
  have eq926680 : ∀ X0 X1 : G, (σ (τ (M.op X0 X1))) = (k (M.op X0 X1) (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X0 X1) (k X0 X1))
       have i₂ := eq925772 X0 X1
       grind)
    | exact superpose eq925772 eq11
    | (have j1 := eq925772 (σ (τ (M.op X0 X1))) (k (M.op X0 X1) (k X0 X1))
       grind)
    | exact resolve eq11 eq925772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925772
  have eq927001 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq926680 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq926680
    | (have j0 := eq926680 (M.op X0 X1) (k (M.op X0 X1) (k X0 X1))
       grind)
    | exact resolve eq926680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926680
  have eq927155 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (k (M.op X0 X1) X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq927001 (M.op x X1) x
       have i₂ := eq443 X1 x
       grind)
    | exact superpose eq443 eq927001
    | (have j0 := eq927001 (M.op X0 X0) (k (M.op X0 X0) (k (M.op X0 X1) X0))
       grind)
    | exact resolve eq927001 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq927001
  have eq1850619 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq927155 X0 X1
       have i₂ := eq406961 X0 X1
       grind)
    | exact superpose eq406961 eq927155
    | (have j0 := eq927155 X0 X1
       have j1 := eq406961 X0 X1
       grind)
    | exact resolve eq927155 eq406961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406961 eq927155
  have eq1851859 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1850619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850619
  have eq1854820 : ∀ X0 X7 : G, (M.op X0 (M.op X7 X7)) = X7 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0 X7
    first
    | (have i₁ := eq12469 x x x x X7 x X0 x
       have i₂ := eq1851859 X0 (M.op x (M.op x (M.op x (M.op x (M.op x (M.op x X7))))))
       grind)
    | exact superpose eq1851859 eq12469
    | (have j1 := eq1851859 X0 x
       grind)
    | exact resolve eq12469 eq1851859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12469
  have eq1886666 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1851859 X0 (M.op X1 X1)
       have i₂ := eq1854820 X0 X1
       grind)
    | exact superpose eq1854820 eq1851859
    | (have j0 := eq1851859 X0 X1
       have j1 := eq1854820 X0 x
       grind)
    | exact resolve eq1851859 eq1854820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851859 eq1854820
  have eq1887578 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1886666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886666
  have eq1891443 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1887578 X0 (σ X1)
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1887578 (σ X0) X1
       grind)
    | exact superpose eq1887578 eq10
    | (have j1 := eq1887578 (τ X0) X1
       grind)
    | exact resolve eq10 eq1887578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887578
  have eq1895874 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1891443 X1 X2
       have i₂ := eq1891443 X1 X0
       grind)
    | (have i₁ := eq1891443 X0 X1
       have i₂ := eq1891443 X0 (τ X0)
       grind)
    | exact superpose eq1891443 eq1891443
    | (have j0 := eq1891443 X1 X1
       have j1 := eq1891443 X1 X1
       grind)
    | exact resolve eq1891443 eq1891443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891443
  have eq1904124 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1895874 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895874
  have eq1919437 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k (M.op X0 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1904124 (k (M.op X0 X0) X0) X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904124
  have eq1919709 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1919437 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919437
  have eq1920575 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1919709 (σ X0)
       grind)
    | exact superpose eq1919709 eq25
    | exact resolve eq25 eq1919709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1920623 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1919709 (τ X0)
       grind)
    | exact superpose eq1919709 eq19
    | exact resolve eq19 eq1919709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1919709
  have eq1944441 : ∀ X0 : G, (M.op X0 X0) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq397635 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq1920575 X0
       grind)
    | exact superpose eq1920575 eq397635
    | (have j0 := eq397635 (M.op X0 X0) (k (τ (M.op (σ X0) (σ X0))) X0)
       grind)
    | exact resolve eq397635 eq1920575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1945025 : ∀ X0 : G, (M.op X0 X0) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1944441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944441
  have eq1945112 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1945025 X0
       have i₂ := eq1920575 X0
       grind)
    | exact superpose eq1920575 eq1945025
    | (have j0 := eq1945025 X0
       grind)
    | exact resolve eq1945025 eq1920575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920575 eq1945025
  have eq1945641 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq397635 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq1920623 X0
       grind)
    | exact superpose eq1920623 eq397635
    | (have j0 := eq397635 (M.op X0 X0) (k (σ (M.op (τ X0) (τ X0))) X0)
       grind)
    | exact resolve eq397635 eq1920623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397635
  have eq1946226 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1945641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945641
  have eq1946304 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1946226 X0
       have i₂ := eq1920623 X0
       grind)
    | exact superpose eq1920623 eq1946226
    | (have j0 := eq1946226 X0
       grind)
    | exact resolve eq1946226 eq1920623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920623 eq1946226
  have eq2134248 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1945112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945112
  have eq2137672 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1946304 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1946304
    | exact resolve eq1946304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946304
  have eq2138480 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq374974
       have i₂ := eq2137672 x
       grind)
    | exact superpose eq2137672 eq374974
    | (have j1 := eq2137672 x
       grind)
    | (have r₁ := eq374974
       have r₂ := eq2137672 x
       grind)
    | exact resolve eq374974 eq2137672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137672
  have eq2139200 : (σ x) = (σ (M.op x x)) := by grind
  clear eq2138480
  have eq2139346 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2139200
       grind)
    | exact superpose eq2139200 eq10
    | exact resolve eq10 eq2139200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2139612 : x = (M.op x x) := by
    first
    | (have i₁ := eq2139346
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2139346
    | exact resolve eq2139346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139346
  have eq2139826 : x ≠ x ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq2134248 x
       have i₂ := eq2139612
       grind)
    | exact superpose eq2139612 eq2134248
    | (have j0 := eq2134248 x
       grind)
    | (have r₁ := eq2134248 x
       have r₂ := eq2139612
       grind)
    | exact resolve eq2134248 eq2139612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134248 eq2139612
  have eq2140193 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq2139826
  have eq2140586 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ x))
       have i₂ := eq2140193
       grind)
    | exact superpose eq2140193 eq11
    | exact resolve eq11 eq2140193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140193
  have eq2144556 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq374974
       have i₂ := eq2140586
       grind)
    | exact superpose eq2140586 eq374974
    | exact resolve eq374974 eq2140586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374974 eq2140586
  have eq2145272 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2144556
       have i₂ := eq2139200
       grind)
    | exact superpose eq2139200 eq2144556
    | (have r₁ := eq2144556
       have r₂ := eq2139200
       grind)
    | exact resolve eq2144556 eq2139200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139200 eq2144556
  have eq2145273 : False := by grind
  exact eq2145273

/-- `Equation1910`: `x = (y ◇ (x ◇ z)) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_pxx_pyx_Equation1910 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1910 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1910.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x X0 y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X2 X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X0 X2)) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op x (M.op X0 y)) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq79 : x = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op x (M.op (M.op X0 (M.op x y)) y)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 x) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) (M.op X0 (M.op x y))) x) = X0 := by
    intro X0
    first
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op X1 X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq100 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq104 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ∨ (k (M.op X1 X2) (M.op X1 (M.op X0 X2))) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op X1 (M.op X0 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op X1 (M.op X0 X2))
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X0 (M.op (M.op X0 X2) X2)) ∨ (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X2) (M.op X1 (M.op X0 X2))) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 X1 X2
       have i₂ := eq53 (M.op X0 X2) X1 X0 X2
       grind)
    | exact superpose eq53 eq104
    | (have j0 := eq104 X0 X1 X2
       grind)
    | (have r₁ := eq104 (M.op X2 (M.op X0 x)) (M.op (M.op X2 (M.op X0 x)) X0) (M.op X2 x)
       have r₂ := eq53 X0 (M.op X2 (M.op X0 x)) X2 x
       grind)
    | exact resolve eq104 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq122 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x x) ∨ (k (M.op (M.op X0 (M.op x y)) y) x) = (M.op (M.op (M.op X0 (M.op x y)) y) (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq80 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op x y)) y) x
       grind)
    | (have r₁ := eq13 (M.op (M.op x (M.op x y)) y) x
       have r₂ := eq80 x
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k (σ (σ X0)) X1) = (σ (σ (k X0 (τ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (σ X0)
       have i₂ := eq48 (τ X1) X0
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq141 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq260 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op (M.op X3 X0) (M.op X1 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op X1 (M.op X0 X2)) X3 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (M.op X0 x) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq79 eq54
    | exact resolve eq54 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 (M.op X1 X2)) X2) X1) = (M.op (M.op (M.op X0 (M.op X1 X2)) X2) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 (M.op X1 X2)) X2) X1
       have i₂ := eq54 X1 X0 X2
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op X1 X2)) X2) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X1 X2)) X2) X1
       have r₂ := eq54 X1 X1 X2
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op (M.op x (M.op x y)) (M.op X0 (M.op x y))) = (M.op (M.op X1 X0) (M.op X1 x)) := by
    intro X0 X1
    first
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq344 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq80 eq82
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq344 eq79
    | exact resolve eq79 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq344
  have eq366 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op (M.op x x) (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq82 (M.op x x) X0
       have i₂ := eq363
       grind)
    | exact superpose eq363 eq82
    | exact resolve eq82 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : (M.op x x) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq263 (M.op x x)
       have i₂ := eq363
       grind)
    | exact superpose eq363 eq263
    | exact resolve eq263 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq368 : ∀ X0 : G, (M.op (M.op x x) (M.op (M.op X0 x) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 (M.op x x) X0 x
       have i₂ := eq363
       grind)
    | exact superpose eq363 eq54
    | exact resolve eq54 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x x) X0 x
       have i₂ := eq363
       grind)
    | exact superpose eq363 eq9
    | exact resolve eq9 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : (M.op x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq89 eq367
    | exact resolve eq367 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq367
  have eq400 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq411 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq412 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq411
  have eq423 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq412
    | exact resolve eq412 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq425 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq423
    | exact resolve eq423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq434 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op X2 (M.op X0 (M.op X1 (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 x) (M.op X2 (M.op X1 (M.op (M.op X0 (M.op x y)) y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (σ x)) (M.op X2 (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq100 eq53
    | exact resolve eq53 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op x (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X4 (M.op X1 X3))) = (M.op (M.op X5 X4) (M.op X5 (M.op (M.op X0 X1) (M.op X0 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X4 X5 X2 (M.op X1 X3)
       have i₂ := eq53 X1 X0 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op x y))) = (M.op (M.op X3 X2) (M.op X3 (M.op (M.op X0 x) (M.op X0 (M.op X1 y))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq82 eq53
    | exact resolve eq53 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 x)) = (M.op (M.op x x) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 (M.op x x) x
       have i₂ := eq363
       grind)
    | exact superpose eq363 eq53
    | exact resolve eq53 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq485 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) = (M.op (M.op X2 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq100 eq53
    | exact resolve eq53 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) = (M.op (M.op X1 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 X1 (M.op X0 (M.op X1 X2)) X2
       have i₂ := eq54 X1 X0 X2
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op X1 y)) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq496 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (σ y))) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq100 eq53
    | exact resolve eq53 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X2))) ∨ (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X2))) = (k X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 (M.op X0 X3)
       have i₂ := eq53 X0 X1 (M.op X0 X3) X3
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X4 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op X4 (M.op X0 X2))
       have i₂ := eq53 X1 X4 X0 X2
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X2)) X2) X1) = (M.op (σ x) (M.op X2 (M.op (M.op X2 (M.op (σ x) (σ y))) (σ y)))) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq276 X0 X1 X2
       have i₂ := eq485 X2 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq485 eq276
    | (have j0 := eq276 X0 X1 X2
       grind)
    | (have r₁ := eq276 (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) (M.op (M.op X2 X1) (M.op X2 X0)) X2
       have r₂ := eq485 X0 X1 X2
       grind)
    | (have r₁ := eq276 (M.op (M.op X2 X1) (M.op X2 X0)) (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) X2
       have r₂ := eq485 X0 X1 X2
       grind)
    | exact resolve eq276 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq548 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) y) x) = (M.op (σ x) (M.op y (M.op (M.op y (M.op (σ x) (σ y))) (σ y)))) ∨ x ≠ X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq485 y y (M.op X0 sF0)
       grind)
    | exact superpose eq485 eq122
    | (have j0 := eq122 X0
       grind)
    | exact resolve eq122 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq485
  have eq553 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) y) x) = (M.op (M.op x y) (M.op x (M.op (σ x) (M.op (M.op y (M.op (σ x) (σ y))) (σ y))))) ∨ x ≠ X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq548 X0
       have i₂ := eq465 sF2 (M.op (M.op y sF4) sF3)
       grind)
    | exact superpose eq465 eq548
    | (have j0 := eq548 X0
       grind)
    | exact resolve eq548 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq548
  have eq555 : ∀ X0 : G, (k (M.op (M.op X0 (M.op x y)) y) x) = (M.op (M.op x y) (M.op x y)) ∨ x ≠ X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq100 eq553
    | (have j0 := eq553 X0
       grind)
    | (have r₁ := eq553 (M.op (σ x) (M.op (M.op x (M.op (σ x) (σ y))) (σ y)))
       have r₂ := eq100 x
       grind)
    | exact resolve eq553 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq556 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op X0 (M.op x y)) y) x) ∨ x ≠ X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq555 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq555
    | (have j0 := eq555 X0
       grind)
    | exact resolve eq555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq557 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq373 eq82
    | exact resolve eq82 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq558 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x X0) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq373 eq53
    | exact resolve eq53 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 : G, (M.op (M.op x (M.op X0 (M.op (M.op x y) y))) (M.op x x)) = X0 := by
    intro X0
    first
    | exact superpose eq373 eq9
    | exact resolve eq9 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq570 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (M.op X0 (M.op (M.op x y) y)) (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq562 X0
       have i₂ := eq287 (M.op X0 (M.op sF0 y)) x
       grind)
    | exact superpose eq287 eq562
    | exact resolve eq562 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq562
  have eq573 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq557
       have i₂ := eq371 x
       grind)
    | exact superpose eq371 eq557
    | exact resolve eq557 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq557
  have eq574 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op x (M.op (M.op x x) (M.op (M.op X0 (M.op (M.op x y) y)) y)))) = X0 := by
    intro X0
    first
    | exact superpose eq366 eq570
    | exact resolve eq570 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq575 : ∀ X0 : G, (M.op x x) = (k (M.op (M.op X0 (M.op x y)) y) x) ∨ x ≠ X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq573 eq556
    | (have j0 := eq556 X0
       grind)
    | exact resolve eq556 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq573
  have eq579 : ∀ X0 : G, (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) y)) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq574 X0
       have i₂ := eq53 sF0 x (M.op x x) (M.op (M.op X0 (M.op sF0 y)) y)
       grind)
    | exact superpose eq53 eq574
    | exact resolve eq574 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq580 : ∀ X0 : G, x ≠ X0 ∨ (M.op x x) = (k (M.op (M.op X0 (M.op x y)) y) x) := by
    intro X0
    first
    | (have j0 := eq575 X0
       have j1 := eq12 (M.op (M.op X0 (M.op x y)) y) x
       grind)
    | (have r₁ := eq575 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq575 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq581 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq579 x
       have i₂ := eq54 sF0 x y
       grind)
    | exact superpose eq54 eq579
    | exact resolve eq579 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq585 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X1 X0) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 X1
       have i₂ := eq581 (M.op X0 x)
       grind)
    | exact superpose eq581 eq479
    | exact resolve eq479 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq587 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq581 (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq581 eq368
    | exact resolve eq368 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq588 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq581 (M.op X0 y)
       grind)
    | exact superpose eq581 eq366
    | exact resolve eq366 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq601 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq585 X0 x
       grind)
    | exact superpose eq585 eq558
    | exact resolve eq558 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq585
  have eq628 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X0 x)) (M.op X2 (M.op X1 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 x) X2 X1 x
       have i₂ := eq587 X0
       grind)
    | exact superpose eq587 eq53
    | exact resolve eq53 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq640 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op x x) X1 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq9
    | exact resolve eq9 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op (M.op x x) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op x x) X0 X1
       have i₂ := eq581 (M.op X0 X1)
       grind)
    | exact superpose eq581 eq53
    | exact resolve eq53 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 (M.op (M.op x x) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op x x) X1
       have i₂ := eq581 (M.op X0 X1)
       grind)
    | exact superpose eq581 eq53
    | exact resolve eq53 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq649 : ∀ X0 X1 : G, (M.op x x) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op x x) X1
       have i₂ := eq581 (M.op X0 X1)
       grind)
    | exact superpose eq581 eq54
    | exact resolve eq54 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x x) X1)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op x x) X0 X1
       have i₂ := eq581 (M.op (M.op X0 (M.op (M.op x x) X1)) X1)
       grind)
    | exact superpose eq581 eq54
    | exact resolve eq54 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : x = (M.op (M.op (M.op x x) (M.op x y)) y) := by
    first
    | (have i₁ := eq52 (M.op x x)
       have i₂ := eq581 y
       grind)
    | exact superpose eq581 eq52
    | exact resolve eq52 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq662 : (M.op x x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq100 (M.op x x)
       have i₂ := eq581 sF4
       grind)
    | exact superpose eq581 eq100
    | exact resolve eq100 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq663 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x x) (σ y))) := by
    first
    | (have i₁ := eq58 (M.op x x)
       have i₂ := eq581 sF4
       grind)
    | exact superpose eq581 eq58
    | exact resolve eq58 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq665 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq663
       have i₂ := eq581 sF3
       grind)
    | exact superpose eq581 eq663
    | exact resolve eq663 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq674 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq655
       have i₂ := eq581 sF0
       grind)
    | exact superpose eq581 eq655
    | exact resolve eq655 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq677 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X1
       have i₂ := eq581 X1
       grind)
    | exact superpose eq581 eq651
    | exact resolve eq651 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq681 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op x x) ∨ (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X2) (M.op X1 (M.op X0 X2))) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 X0 X1 X2
       have i₂ := eq649 X0 X2
       grind)
    | exact superpose eq649 eq119
    | (have j0 := eq119 X0 X1 X2
       grind)
    | (have r₁ := eq119 (M.op x x) x x
       have r₂ := eq649 x x
       grind)
    | exact resolve eq119 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq687 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq648 X0 X1 X2
       have i₂ := eq581 X1
       grind)
    | exact superpose eq581 eq648
    | exact resolve eq648 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq688 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq581 X2
       grind)
    | exact superpose eq581 eq647
    | exact resolve eq647 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq698 : (M.op x x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq665 eq662
    | exact resolve eq662 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq705 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq649 X0 x
       have i₂ := eq677 X0 x
       grind)
    | exact superpose eq677 eq649
    | exact resolve eq649 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq706 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k X3 (M.op X1 X2)) ∨ (M.op X1 X2) ≠ (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq503 X0 X0 X1 X3
       have i₂ := eq677 X0 X1
       grind)
    | exact superpose eq677 eq503
    | (have j0 := eq503 X0 X1 X2 X3
       grind)
    | exact resolve eq503 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq708 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (M.op X1 (M.op X0 X2)) = (M.op x x) ∨ (M.op x x) = (k (M.op X1 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq681 X0 X1 X2
       have i₂ := eq640 X2 X1
       grind)
    | exact superpose eq640 eq681
    | (have j0 := eq681 X0 X1 X2
       grind)
    | (have r₁ := eq681 (M.op x x) (M.op (M.op x x) X0) X0
       have r₂ := eq640 X0 (M.op x x)
       grind)
    | exact resolve eq681 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq681
  have eq724 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X4 (M.op X1 X3))) = (M.op (M.op X5 X4) (M.op X5 (M.op X1 (M.op X2 X3)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq470 x X1 X2 X3 X4 X5
       have i₂ := eq687 X1 (M.op X2 X3) x
       grind)
    | exact superpose eq687 eq470
    | exact resolve eq470 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq740 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 x) (M.op X0 (M.op X1 y)))) = (M.op X1 (M.op X2 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 X0 X1 X2 x
       have i₂ := eq687 X2 (M.op (M.op X0 x) (M.op X0 (M.op X1 y))) x
       grind)
    | exact superpose eq687 eq471
    | exact resolve eq471 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq747 : ∀ X0 X1 X2 X4 : G, (M.op X4 X1) = (M.op (M.op X0 (M.op X1 X2)) (M.op X4 (M.op X0 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq521 X0 X1 X2 x X4
       have i₂ := eq687 (M.op X0 (M.op X1 X2)) (M.op X4 (M.op X0 X2)) x
       grind)
    | exact superpose eq687 eq521
    | exact resolve eq521 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq749 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 x) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1 x
       have i₂ := eq687 (M.op X0 x) (M.op X1 x) x
       grind)
    | exact superpose eq687 eq628
    | exact resolve eq628 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq751 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1 x
       have i₂ := eq687 (M.op X1 sF4) (M.op X0 (M.op X1 sF3)) x
       grind)
    | exact superpose eq687 eq434
    | exact resolve eq434 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq764 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op X1 (M.op (M.op X0 (M.op x y)) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1 x
       have i₂ := eq687 x (M.op X1 (M.op (M.op X0 sF0) y)) x
       grind)
    | exact superpose eq687 eq441
    | exact resolve eq441 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq768 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X1 x
       have i₂ := eq687 sF2 (M.op X1 (M.op (M.op X0 sF4) sF3)) x
       grind)
    | exact superpose eq687 eq443
    | exact resolve eq443 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq770 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq687 X0 X1 X2
       have i₂ := eq688 (M.op X2 X0) X1 X2
       grind)
    | (have i₁ := eq687 X0 X1 X2
       have i₂ := eq688 X2 X1 (M.op X2 X0)
       grind)
    | exact superpose eq688 eq687
    | exact resolve eq687 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq779 : (σ x) = (M.op x x) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq698 eq418
    | exact resolve eq418 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq780 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) := by
    first
    | exact superpose eq698 eq425
    | exact resolve eq425 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq698
  have eq786 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X0 X1) X1)) = (k X3 (M.op X1 X2)) ∨ (M.op X1 X2) ≠ (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq706 X0 X1 X2 X3
       have i₂ := eq688 (M.op X0 X1) X1 X0
       grind)
    | (have i₁ := eq706 X0 X1 X2 X3
       have i₂ := eq688 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq688 eq706
    | (have j0 := eq706 X0 X1 X2 X3
       grind)
    | exact resolve eq706 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq787 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op x x) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq705 (σ X0)
       grind)
    | exact superpose eq705 eq400
    | (have j0 := eq400 X0 X1
       grind)
    | exact resolve eq400 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq792 : (k y x) = (M.op x x) ∨ x ≠ (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq705 y
       grind)
    | exact superpose eq705 eq103
    | exact resolve eq103 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq802 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X0 (M.op X1 X2)) X2) X1) = (M.op X2 X2) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq768 eq547
    | (have j0 := eq547 X0 X1 X2
       grind)
    | (have r₁ := eq547 (M.op X1 X0) (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) X2
       have r₂ := eq768 X0 X1
       grind)
    | (have r₁ := eq547 (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) (M.op X1 X0) X2
       have r₂ := eq768 X0 X1
       grind)
    | exact resolve eq547 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq768
  have eq816 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x y))) = (M.op X2 (M.op X0 (M.op (M.op X0 x) (M.op X1 y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq740 X0 X1 X2
       have i₂ := eq688 (M.op X0 x) (M.op X1 y) X0
       grind)
    | (have i₁ := eq740 X0 X1 X2
       have i₂ := eq688 X0 (M.op X1 y) (M.op X0 x)
       grind)
    | exact superpose eq688 eq740
    | exact resolve eq740 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq822 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X4 (M.op X1 X3))) = (M.op X5 (M.op (M.op X5 X4) (M.op X1 (M.op X2 X3)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq724 X1 X2 X3 X4 X5
       have i₂ := eq688 (M.op X5 X4) (M.op X1 (M.op X2 X3)) X5
       grind)
    | (have i₁ := eq724 X1 X2 X3 X4 X5
       have i₂ := eq688 X5 (M.op X1 (M.op X2 X3)) (M.op X5 X4)
       grind)
    | exact superpose eq688 eq724
    | exact resolve eq724 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq843 : (σ (k x x)) = (M.op x x) ∨ (σ x) = (M.op x x) := by
    first
    | (have i₁ := eq779
       have i₂ := eq705 sF2
       grind)
    | exact superpose eq705 eq779
    | exact resolve eq779 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq847 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (k X3 (M.op X1 X2)) ∨ (M.op X1 X2) ≠ (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq786 X0 X1 X2 X3
       have i₂ := eq770 X1 X1 X0
       grind)
    | exact superpose eq770 eq786
    | (have j0 := eq786 X0 X1 X2 X3
       grind)
    | exact resolve eq786 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq850 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq792
       have r₂ := eq12 x x
       grind)
    | exact resolve eq792 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq859 : ∀ X1 X2 : G, (M.op X1 (M.op X2 (M.op x y))) = (M.op X2 (M.op x (M.op X1 y))) := by
    intro X1 X2
    first
    | (have i₁ := eq816 x X1 X2
       have i₂ := eq770 x (M.op X1 y) x
       grind)
    | exact superpose eq770 eq816
    | exact resolve eq816 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq861 : ∀ X1 X2 X3 X4 : G, (M.op X4 (M.op X1 (M.op X2 X3))) = (M.op X2 (M.op X4 (M.op X1 X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq822 X1 X2 X3 X4 x
       have i₂ := eq770 X4 (M.op X1 (M.op X2 X3)) x
       grind)
    | exact superpose eq770 eq822
    | exact resolve eq822 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq866 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2))) ∨ (M.op X1 X1) = (k X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq847 X0 X1 X2 X3
       have i₂ := eq688 (M.op X0 X1) (M.op (M.op X1 X2) X2) X0
       grind)
    | (have i₁ := eq847 X0 X1 X2 X3
       have i₂ := eq688 X0 (M.op (M.op X1 X2) X2) (M.op X0 X1)
       grind)
    | exact superpose eq688 eq847
    | (have j0 := eq847 X0 X1 X2 X3
       grind)
    | exact resolve eq847 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq878 : ∀ X0 X1 X2 X4 : G, (M.op X4 X1) = (M.op X0 (M.op (M.op X0 (M.op X1 X2)) (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq747 X0 X1 X2 X4
       have i₂ := eq861 X4 X0 X2 (M.op X0 (M.op X1 X2))
       grind)
    | (have i₁ := eq747 X1 X1 x X4
       have i₂ := eq861 X1 (M.op X1 (M.op X1 x)) x X4
       grind)
    | exact superpose eq861 eq747
    | exact resolve eq747 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq879 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X1 (M.op X0 X2)) (M.op (M.op X3 X0) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq260 X0 X1 X2 X3
       have i₂ := eq861 (M.op X3 X0) X1 X2 (M.op X1 (M.op X0 X2))
       grind)
    | (have i₁ := eq260 X0 X1 X3 X3
       have i₂ := eq861 X1 (M.op X1 (M.op X0 X3)) X3 (M.op X3 X0)
       grind)
    | exact superpose eq861 eq260
    | exact resolve eq260 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq885 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq751 X1 x
       have i₂ := eq861 X1 x sF3 (M.op x sF4)
       grind)
    | (have i₁ := eq751 x X1
       have i₂ := eq861 X1 (M.op X1 sF4) sF3 x
       grind)
    | exact superpose eq861 eq751
    | exact resolve eq751 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq887 : ∀ X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X1 (M.op (M.op X1 X2) X2)) ∨ (M.op X1 X1) = (k X3 (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq866 x X1 X2 X3
       have i₂ := eq770 X1 (M.op (M.op X1 X2) X2) x
       grind)
    | exact superpose eq770 eq866
    | (have j0 := eq866 x X1 X2 X3
       grind)
    | exact resolve eq866 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq889 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq885 X0 x
       have i₂ := eq770 sF4 (M.op X0 sF3) x
       grind)
    | exact superpose eq770 eq885
    | exact resolve eq885 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq894 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X3 X0) X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq879 X0 x X2 X3
       have i₂ := eq770 (M.op X0 X2) (M.op (M.op X3 X0) X2) x
       grind)
    | exact superpose eq770 eq879
    | exact resolve eq879 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq895 : ∀ X1 X2 X4 : G, (M.op X4 X1) = (M.op (M.op X1 X2) (M.op X4 X2)) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq878 x X1 X2 X4
       have i₂ := eq770 (M.op X1 X2) (M.op X4 X2) x
       grind)
    | exact superpose eq770 eq878
    | exact resolve eq878 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq899 : ∀ X1 X2 X3 : G, (M.op X1 X2) ≠ (M.op X2 X2) ∨ (M.op X1 X1) = (k X3 (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq887 X1 X2 X3
       have i₂ := eq770 X2 X2 X1
       grind)
    | exact superpose eq770 eq887
    | (have j0 := eq887 X1 X2 X3
       grind)
    | (have r₁ := eq887 X2 X2 X3
       have r₂ := eq770 X2 X2 X2
       grind)
    | exact resolve eq887 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq936 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq705 X1
       have i₂ := eq705 X0
       grind)
    | (have i₁ := eq705 X0
       have i₂ := eq705 x
       grind)
    | exact superpose eq705 eq705
    | exact resolve eq705 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X1
       have i₂ := eq705 X0
       grind)
    | (have i₁ := eq581 X0
       have i₂ := eq705 x
       grind)
    | exact superpose eq705 eq581
    | exact resolve eq581 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq969 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq936 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq936 X0 X1
       grind)
    | exact superpose eq936 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq936 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq936 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq944 X0 (M.op X0 X0)
       grind)
    | exact superpose eq944 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq944 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq995 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1056 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq889 sF3
       have i₂ := eq936 X0 sF3
       grind)
    | (have i₁ := eq889 sF3
       have i₂ := eq936 sF3 x
       grind)
    | exact superpose eq936 eq889
    | exact resolve eq889 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : ∀ X0 : G, (M.op y x) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq601 y
       have i₂ := eq936 X0 y
       grind)
    | (have i₁ := eq601 y
       have i₂ := eq936 y X0
       grind)
    | exact superpose eq936 eq601
    | exact resolve eq601 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X0 X0) X1
       have i₂ := eq1003 X0 (σ X1)
       grind)
    | exact superpose eq1003 eq48
    | exact resolve eq48 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (M.op X0 X0)
       have i₂ := eq1003 X0 (τ X1)
       grind)
    | exact superpose eq1003 eq49
    | exact resolve eq49 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1056 eq677
    | exact resolve eq677 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1242 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op y x) X0)) := by
    intro X0
    first
    | exact superpose eq1122 eq54
    | exact resolve eq54 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1245 : ∀ X0 : G, (M.op x y) = (M.op (M.op y x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1122 eq677
    | exact resolve eq677 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1227 eq54
    | exact resolve eq54 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1383 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 (M.op y x) X0
       have i₂ := eq1245 X0
       grind)
    | exact superpose eq1245 eq54
    | exact resolve eq54 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1245
  have eq1473 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op x x) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq787 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq787
    | (have j0 := eq787 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq787 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (M.op x x) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq787 (τ X0) X1
       grind)
    | exact superpose eq787 eq48
    | (have j1 := eq787 (τ X0) X1
       grind)
    | exact resolve eq48 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq787
  have eq1507 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (M.op x x) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1493 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1493
    | (have j0 := eq1493 X0 X1
       grind)
    | exact resolve eq1493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1520 : ∀ X0 X1 : G, (M.op x x) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1507 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1507
    | (have j0 := eq1507 X0 X1
       grind)
    | exact resolve eq1507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq1535 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op x x) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1520 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1520
    | (have j0 := eq1520 X0 X1
       grind)
    | exact resolve eq1520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq1903 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op x x) = X0 ∨ (M.op x x) = (k (M.op (M.op X1 X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq708 (M.op x X0) (M.op X0 X2) X2
       have i₂ := eq894 X0 X2 x
       grind)
    | exact superpose eq894 eq708
    | exact resolve eq708 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq1912 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op x x) = (k (M.op (M.op X1 X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1903 X0 X1 X2
       have j1 := eq969 x X0 (M.op (M.op X1 X2) X2)
       grind)
    | (have r₁ := eq1903 (k X2 X1) (k X2 X1) X2
       have r₂ := eq969 (k X2 X1) X1 X2
       grind)
    | (have r₁ := eq1903 X1 X1 X2
       have r₂ := eq969 x X1 X2
       grind)
    | (have r₁ := eq1903 (M.op X0 X0) X1 X2
       have r₂ := eq969 X0 (M.op x x) X2
       grind)
    | exact resolve eq1903 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq1903
  have eq1968 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op x x) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1912 X0 X1 x
       have i₂ := eq677 X1 x
       grind)
    | exact superpose eq677 eq1912
    | (have j0 := eq1912 X0 X1 x
       grind)
    | exact resolve eq1912 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq2015 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op X0 (M.op (M.op y x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq895 X1 (M.op (M.op y x) X1) X0
       have i₂ := eq1242 X1
       grind)
    | exact superpose eq1242 eq895
    | exact resolve eq895 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2055 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq895 X2 X1 (M.op X0 X1)
       have i₂ := eq677 X0 X1
       grind)
    | exact superpose eq677 eq895
    | exact resolve eq895 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2097 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op (M.op y X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq588 X1
       have i₂ := eq895 y X0 X1
       grind)
    | exact superpose eq895 eq588
    | exact resolve eq588 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2125 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X2)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq894 X2 (M.op X0 X2) X1
       have i₂ := eq895 X1 X2 X0
       grind)
    | exact superpose eq895 eq894
    | exact resolve eq894 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2152 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 X2)) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2125 X0 X1 X2
       have i₂ := eq688 (M.op X2 (M.op X0 X2)) X1 X0
       grind)
    | (have i₁ := eq2125 X0 X1 X2
       have i₂ := eq688 X0 X1 (M.op X2 (M.op X0 X2))
       grind)
    | exact superpose eq688 eq2125
    | exact resolve eq2125 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2432 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2152 (M.op X0 X1) X2 X1
       have i₂ := eq677 X0 X1
       grind)
    | exact superpose eq677 eq2152
    | exact resolve eq2152 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2478 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op (M.op x y) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq1383 eq2152
    | exact resolve eq2152 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2479 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq1332 eq2152
    | exact resolve eq2152 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq2152
  have eq2833 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X1 x) (M.op X2 (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq688 (M.op X1 x) (M.op X0 x) X2
       have i₂ := eq749 X1 X0
       grind)
    | exact superpose eq749 eq688
    | exact resolve eq688 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2842 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op (M.op x y) (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | exact superpose eq601 eq688
    | exact resolve eq688 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3077 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y x) X1)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq1383 eq770
    | exact resolve eq770 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq3083 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq770 (M.op X0 X2) X3 (M.op X1 X2)
       have i₂ := eq895 X1 X2 X0
       grind)
    | exact superpose eq895 eq770
    | exact resolve eq770 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3084 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X1 X2) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq770 (M.op (M.op X0 X1) X2) X3 (M.op X1 X2)
       have i₂ := eq894 X1 X2 X0
       grind)
    | exact superpose eq894 eq770
    | exact resolve eq770 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3085 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X1 x) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq770 (M.op X0 x) X2 (M.op X1 x)
       have i₂ := eq749 X1 X0
       grind)
    | exact superpose eq749 eq770
    | exact resolve eq770 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3094 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq601 eq770
    | exact resolve eq770 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3101 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq889 eq770
    | exact resolve eq770 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3105 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq770 X2 (M.op X0 X2) X1
       have i₂ := eq895 X1 X2 X0
       grind)
    | exact superpose eq895 eq770
    | exact resolve eq770 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3106 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq770 X1 (M.op (M.op X0 X2) X1) X2
       have i₂ := eq894 X2 X1 X0
       grind)
    | exact superpose eq894 eq770
    | exact resolve eq770 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3121 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (M.op y x) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 (M.op (M.op y x) (M.op X1 X0)) X1
       have i₂ := eq1242 (M.op X1 X0)
       grind)
    | exact superpose eq1242 eq770
    | exact resolve eq770 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq3621 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op (M.op X2 X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688 X3 X0 (M.op X2 X1)
       have i₂ := eq2055 X2 X1 X0
       grind)
    | (have i₁ := eq688 X3 X0 (M.op X2 X1)
       have i₂ := eq2055 X0 X1 X2
       grind)
    | exact superpose eq2055 eq688
    | exact resolve eq688 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3629 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq895 X0 X3 (M.op X2 X1)
       have i₂ := eq2055 X2 X1 X0
       grind)
    | (have i₁ := eq895 X0 X3 (M.op X2 X1)
       have i₂ := eq2055 X0 X1 X2
       grind)
    | exact superpose eq2055 eq895
    | exact resolve eq895 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3636 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op (M.op x y) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 (M.op X1 X0)
       have i₂ := eq2055 X1 X0 y
       grind)
    | (have i₁ := eq601 (M.op X1 X0)
       have i₂ := eq2055 y X0 X1
       grind)
    | exact superpose eq2055 eq601
    | exact resolve eq601 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3872 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X3) (M.op X1 (M.op (M.op X3 X2) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq688 X1 (M.op (M.op X3 X2) X0) (M.op X2 X3)
       have i₂ := eq2432 X2 X3 X0
       grind)
    | exact superpose eq2432 eq688
    | exact resolve eq688 eq2432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3874 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op (M.op X2 X1) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq770 (M.op (M.op X1 X2) X0) X3 (M.op X2 X1)
       have i₂ := eq2432 X2 X1 X0
       grind)
    | exact superpose eq2432 eq770
    | exact resolve eq770 eq2432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3897 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X0 X3)) = (M.op (M.op X2 X0) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3874 X1 X0 X2 X3
       have i₂ := eq3084 X0 X2 X1 X3
       grind)
    | exact superpose eq3084 eq3874
    | exact resolve eq3874 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq4467 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ (τ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq134 X0 (σ X1)
       grind)
    | exact superpose eq134 eq15
    | exact resolve eq15 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq4489 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4467 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4467
    | exact resolve eq4467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4675 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X3)) = (M.op (M.op (M.op X1 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq770 (M.op (M.op X1 X0) X2) X3 X2
       have i₂ := eq3106 X1 X2 X0
       grind)
    | exact superpose eq3106 eq770
    | exact resolve eq770 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4713 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X1 X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4675 X0 X1 X2 X3
       have i₂ := eq3084 X1 X0 X2 X3
       grind)
    | exact superpose eq3084 eq4675
    | exact resolve eq4675 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq5786 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ (M.op X0 X0)))
       have i₂ := eq1209 X0 X1
       grind)
    | exact superpose eq1209 eq10
    | exact resolve eq10 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq5879 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (σ (M.op X0 X0))
       have i₂ := eq1210 X0 (τ X1)
       grind)
    | exact superpose eq1210 eq49
    | exact resolve eq49 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7039 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op x x) := by
    first
    | exact superpose eq26 eq1968
    | (have j0 := eq1968 (σ x) (σ y)
       grind)
    | exact resolve eq1968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq7046 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op x x) := by
    first
    | exact superpose eq61 eq7039
    | exact resolve eq7039 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7039
  have eq7767 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X1 X0)) X2) = (M.op (M.op X2 (M.op x y)) (M.op (M.op y X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 X2 (M.op X1 X0)
       have i₂ := eq2055 X1 X0 y
       grind)
    | (have i₁ := eq495 X2 (M.op X1 X0)
       have i₂ := eq2055 y X0 X1
       grind)
    | exact superpose eq2055 eq495
    | exact resolve eq495 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7796 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X2 (M.op x y)) (M.op (M.op X1 x) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 X2 (M.op X1 x)
       have i₂ := eq3105 X1 X0 x
       grind)
    | (have i₁ := eq495 X2 (M.op X1 x)
       have i₂ := eq3105 X1 x X0
       grind)
    | exact superpose eq3105 eq495
    | exact resolve eq495 eq3105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq7802 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 (M.op x y)) (M.op (M.op (M.op X1 X0) x) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 X2 (M.op (M.op X1 X0) x)
       have i₂ := eq3106 X1 x X0
       grind)
    | exact superpose eq3106 eq495
    | exact resolve eq495 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7838 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq495 eq688
    | exact resolve eq688 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8006 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 (M.op x y)) (M.op (M.op y x) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7802 X0 X1 X2
       have i₂ := eq2055 (M.op X1 X0) x y
       grind)
    | (have i₁ := eq7802 X0 X1 X2
       have i₂ := eq2055 y x (M.op X1 X0)
       grind)
    | exact superpose eq2055 eq7802
    | exact resolve eq7802 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7802
  have eq8332 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq496 eq688
    | exact resolve eq688 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq9075 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op x y)) y))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq764 eq2055
    | exact resolve eq2055 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq9088 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x (M.op x y)) (M.op (M.op y x) (M.op (M.op X0 (M.op (M.op X1 (M.op x y)) y)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9075 X0 X1 X0
       have i₂ := eq8006 X0 (M.op X0 (M.op (M.op X1 sF0) y)) x
       grind)
    | exact superpose eq8006 eq9075
    | exact resolve eq9075 eq8006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8006 eq9075
  have eq9156 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x (M.op x y)) (M.op (M.op X0 (M.op y x)) (M.op (M.op (M.op X1 (M.op x y)) y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9088 X0 X1 x
       have i₂ := eq4713 X0 (M.op (M.op X1 sF0) y) (M.op y x) x
       grind)
    | exact superpose eq4713 eq9088
    | exact resolve eq9088 eq4713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9088
  have eq9207 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op x (M.op x y))) (M.op (M.op y x) (M.op (M.op (M.op X1 (M.op x y)) y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9156 X0 X1 X2
       have i₂ := eq4713 X0 (M.op y x) (M.op x sF0) (M.op (M.op (M.op X1 sF0) y) X2)
       grind)
    | exact superpose eq4713 eq9156
    | exact resolve eq9156 eq4713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9156
  have eq9256 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op x (M.op x y))) (M.op (M.op (M.op X1 (M.op x y)) x) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9207 X0 X1 X2
       have i₂ := eq3085 (M.op X1 sF0) y X2
       grind)
    | exact superpose eq3085 eq9207
    | exact resolve eq9207 eq3085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085 eq9207
  have eq9276 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op x (M.op x y))) (M.op (M.op (M.op x y) x) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9256 X0 X0 x
       have i₂ := eq3084 X0 sF0 x x
       grind)
    | exact superpose eq3084 eq9256
    | exact resolve eq9256 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9256
  have eq9286 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op x (M.op x y))) (M.op x (M.op (M.op y x) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3077 eq9276
    | exact resolve eq9276 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9276
  have eq9289 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9286 X2 X1 X2
       have i₂ := eq3897 x (M.op x sF0) X2 (M.op (M.op y x) (M.op X1 X2))
       grind)
    | (have i₁ := eq9286 X2 X1 X2
       have i₂ := eq3897 (M.op x sF0) x X2 (M.op (M.op y x) (M.op X1 X2))
       grind)
    | exact superpose eq3897 eq9286
    | exact resolve eq9286 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897 eq9286
  have eq9993 : (k x x) = (τ (M.op x x)) ∨ (σ x) = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq843
       grind)
    | exact superpose eq843 eq10
    | exact resolve eq10 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq10197 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op X1 y)) = (M.op X0 (M.op x (M.op (M.op x X1) y))) := by
    intro X0 X1
    first
    | exact superpose eq859 eq495
    | exact resolve eq495 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq10360 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10197 X0 X1
       have i₂ := eq770 X1 y x
       grind)
    | exact superpose eq770 eq10197
    | exact resolve eq10197 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10197
  have eq10543 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) (M.op (M.op x y) (M.op X1 y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10360 X0 X1
       have i₂ := eq9289 (M.op X0 sF0) sF0 (M.op X1 y)
       grind)
    | exact superpose eq9289 eq10360
    | exact resolve eq10360 eq9289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10360
  have eq10663 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op x y) x) (M.op X0 (M.op (M.op x (M.op x y)) (M.op (M.op y x) (M.op (M.op x y) (M.op X1 y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10543 X0 X1
       have i₂ := eq3084 X0 sF0 x (M.op (M.op x sF0) (M.op (M.op y x) (M.op sF0 (M.op X1 y))))
       grind)
    | exact superpose eq3084 eq10543
    | exact resolve eq10543 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10543
  have eq10739 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op (M.op y x) (M.op (M.op x y) (M.op X1 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10663 X1 X1
       have i₂ := eq3872 (M.op (M.op y x) (M.op sF0 (M.op X1 y))) X1 sF0 x
       grind)
    | exact superpose eq3872 eq10663
    | exact resolve eq10663 eq3872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3872 eq10663
  have eq10787 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op (M.op x y) (M.op (M.op y x) (M.op X1 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10739 X0 X1
       have i₂ := eq688 (M.op y x) (M.op X1 y) sF0
       grind)
    | (have i₁ := eq10739 X0 X1
       have i₂ := eq688 sF0 (M.op X1 y) (M.op y x)
       grind)
    | exact superpose eq688 eq10739
    | exact resolve eq10739 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10739
  have eq10820 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op (M.op y x) (M.op X1 x))) := by
    intro X0 X1
    first
    | exact superpose eq2842 eq10787
    | exact resolve eq10787 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787
  have eq15847 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 (M.op x y)) (M.op (M.op (M.op y X2) (M.op X0 X2)) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 X1 (M.op (M.op y X2) (M.op X0 X2))
       have i₂ := eq2097 X2 X0
       grind)
    | exact superpose eq2097 eq495
    | exact resolve eq495 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097
  have eq15901 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 (M.op x y)) (M.op (M.op y x) (M.op (M.op (M.op y X2) (M.op X0 X2)) x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15847 X0 X1 X2
       have i₂ := eq10820 (M.op X1 sF0) (M.op (M.op y X2) (M.op X0 X2))
       grind)
    | exact superpose eq10820 eq15847
    | exact resolve eq15847 eq10820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15847
  have eq16074 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 (M.op x y)) (M.op (M.op y (M.op X0 X2)) (M.op y X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15901 X0 X1 X2
       have i₂ := eq3629 y (M.op X0 X2) (M.op y X2) x
       grind)
    | exact superpose eq3629 eq15901
    | exact resolve eq15901 eq3629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq16203 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op y (M.op (M.op X1 (M.op x y)) (M.op (M.op y (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16074 X0 X1 x
       have i₂ := eq861 (M.op y (M.op X0 x)) y x (M.op X1 sF0)
       grind)
    | (have i₁ := eq16074 X0 X1 x
       have i₂ := eq861 y (M.op X1 sF0) x (M.op y (M.op X0 x))
       grind)
    | exact superpose eq861 eq16074
    | exact resolve eq16074 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16074
  have eq16310 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 y) (M.op (M.op x y) (M.op (M.op y (M.op X0 X2)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16203 X0 X0 X2
       have i₂ := eq4713 X0 sF0 y (M.op (M.op y (M.op X0 X2)) X2)
       grind)
    | exact superpose eq4713 eq16203
    | exact resolve eq16203 eq4713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4713 eq16203
  have eq16376 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op x y) (M.op (M.op y (M.op X0 X2)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16310 X0 X0 X2
       have i₂ := eq3094 X0 (M.op sF0 (M.op (M.op y (M.op X0 X2)) X2))
       grind)
    | exact superpose eq3094 eq16310
    | exact resolve eq16310 eq3094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16310
  have eq16428 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op y (M.op X0 X2)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16376 X0 X1 X2
       have i₂ := eq861 (M.op X1 x) sF0 (M.op (M.op y (M.op X0 X2)) X2) sF0
       grind)
    | (have i₁ := eq16376 X0 X1 X2
       have i₂ := eq861 sF0 sF0 (M.op (M.op y (M.op X0 X2)) X2) (M.op X1 x)
       grind)
    | exact superpose eq861 eq16376
    | exact resolve eq16376 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq16473 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op y x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) (M.op (M.op X0 X2) X2))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16428 X0 X1 X2
       have i₂ := eq9289 y (M.op X0 X2) X2
       grind)
    | exact superpose eq9289 eq16428
    | exact resolve eq16428 eq9289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9289 eq16428
  have eq16510 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) (M.op (M.op X0 X2) X2))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2015 eq16473
    | exact resolve eq16473 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015 eq16473
  have eq16542 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16510 X0 X1 x
       have i₂ := eq677 X0 x
       grind)
    | exact superpose eq677 eq16510
    | exact resolve eq16510 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16510
  have eq19359 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq9993
       have i₂ := eq936 X0 x
       grind)
    | (have i₁ := eq9993
       have i₂ := eq936 x x
       grind)
    | exact superpose eq936 eq9993
    | exact resolve eq9993 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9993
  have eq22090 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X2 (M.op X0 (M.op X1 y)))) = (M.op X2 (M.op X0 (M.op X1 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2842 eq688
    | exact resolve eq688 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25431 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op y (M.op x y)) y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2842 (M.op x X0) X1
       have i₂ := eq7838 X0 y
       grind)
    | exact superpose eq7838 eq2842
    | exact resolve eq2842 eq7838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842
  have eq25488 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op y (M.op x y)) x))) := by
    intro X0 X1
    first
    | exact superpose eq22090 eq25431
    | exact resolve eq25431 eq22090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25431
  have eq25734 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op x y) (M.op (M.op x x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) y)))))) := by
    intro X0 X1
    first
    | exact superpose eq16542 eq25488
    | exact resolve eq25488 eq16542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16542 eq25488
  have eq25926 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op x x) (M.op (M.op x (M.op x y)) (M.op (M.op y x) x))))) := by
    intro X0 X1
    first
    | exact superpose eq22090 eq25734
    | exact resolve eq25734 eq22090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25734
  have eq26088 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op x (M.op x y)) (M.op (M.op y x) x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25926 X0 X1
       have i₂ := eq2833 (M.op y x) x (M.op x sF0)
       grind)
    | exact superpose eq2833 eq25926
    | exact resolve eq25926 eq2833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25926
  have eq26227 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op x (M.op x x)) x))) := by
    intro X0 X1
    first
    | exact superpose eq7767 eq26088
    | exact resolve eq26088 eq7767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7767 eq26088
  have eq26333 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op x (M.op x y)) (M.op (M.op x x) y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26227 X0 X1
       have i₂ := eq7796 x x x
       grind)
    | exact superpose eq7796 eq26227
    | exact resolve eq26227 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7796 eq26227
  have eq26555 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) x)) = (M.op X1 (M.op X0 (M.op (M.op x (M.op x y)) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq26333 X0 X1
       have i₂ := eq3083 x x sF0 y
       grind)
    | exact superpose eq3083 eq26333
    | exact resolve eq26333 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083 eq26333
  have eq34980 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2055 X1 X0 x
       have i₂ := eq3636 X0 X1
       grind)
    | exact superpose eq3636 eq2055
    | exact resolve eq2055 eq3636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq44346 : ∀ X0 : G, (M.op X0 X0) = (σ (k x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq19359 X0
       grind)
    | exact superpose eq19359 eq11
    | (have j1 := eq19359 X0
       grind)
    | exact resolve eq11 eq19359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19359
  have eq55231 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op x X0) X1)) = (M.op (M.op x y) (M.op X2 (M.op (M.op y X0) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq34980 eq688
    | exact resolve eq688 eq34980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34980
  have eq57056 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k x x)) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X1 X0
       have i₂ := eq44346 X1
       grind)
    | exact superpose eq44346 eq936
    | (have j1 := eq44346 X0
       grind)
    | exact resolve eq936 eq44346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57057 : ∀ X0 X1 : G, (M.op (σ (k x x)) X1) = X1 ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq44346 X0
       grind)
    | exact superpose eq44346 eq944
    | (have j1 := eq44346 X0
       grind)
    | exact resolve eq944 eq44346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44346
  have eq57868 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X4) (M.op X2 (M.op X0 X3))) = (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq486 (M.op X2 (M.op X0 X3)) X1 X3 X4
       have i₂ := eq486 X2 X0 X3 X1
       grind)
    | exact superpose eq486 eq486
    | exact resolve eq486 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq58939 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X4) (M.op X2 (M.op X0 X3))) = (M.op (M.op X1 X2) (M.op X0 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57868 X0 X1 X2 X3 X4
       have i₂ := eq3084 X0 X1 X2 (M.op X4 X3)
       grind)
    | exact superpose eq3084 eq57868
    | exact resolve eq57868 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq57868
  have eq74703 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 (M.op x y)) (M.op (M.op (M.op y x) (M.op X0 x)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq495 X1 (M.op (M.op y x) (M.op X0 x))
       have i₂ := eq3121 x X0
       grind)
    | exact superpose eq3121 eq495
    | exact resolve eq495 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq74738 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 (M.op x y)) (M.op (M.op y x) (M.op (M.op (M.op y x) (M.op X0 x)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq74703 X0 X1
       have i₂ := eq10820 (M.op X1 sF0) (M.op (M.op y x) (M.op X0 x))
       grind)
    | exact superpose eq10820 eq74703
    | exact resolve eq74703 eq10820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10820 eq74703
  have eq75036 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 (M.op x y)) (M.op (M.op y (M.op X0 x)) (M.op y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq74738 X0 X1
       have i₂ := eq3629 y (M.op X0 x) (M.op y x) x
       grind)
    | exact superpose eq3629 eq74738
    | exact resolve eq74738 eq3629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629 eq74738
  have eq75274 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 y) (M.op (M.op x y) (M.op (M.op y (M.op X0 x)) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq75036 X0 X1
       have i₂ := eq58939 y X1 (M.op y (M.op X0 x)) x sF0
       grind)
    | (have i₁ := eq75036 X0 X1
       have i₂ := eq58939 (M.op y (M.op X0 x)) X1 sF0 x y
       grind)
    | exact superpose eq58939 eq75036
    | exact resolve eq75036 eq58939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58939 eq75036
  have eq75458 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op x y) (M.op (M.op y (M.op X0 x)) x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq75274 X0 X0
       have i₂ := eq3094 X0 (M.op sF0 (M.op (M.op y (M.op X0 x)) x))
       grind)
    | exact superpose eq3094 eq75274
    | exact resolve eq75274 eq3094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75274
  have eq75596 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op y (M.op X0 x)) x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq75458 X0 X1
       have i₂ := eq861 (M.op X1 x) sF0 (M.op (M.op y (M.op X0 x)) x) sF0
       grind)
    | (have i₁ := eq75458 X0 X1
       have i₂ := eq861 sF0 sF0 (M.op (M.op y (M.op X0 x)) x) (M.op X1 x)
       grind)
    | exact superpose eq861 eq75458
    | exact resolve eq75458 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq75458
  have eq75711 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op x (M.op X0 x)) x))) := by
    intro X0 X1
    first
    | exact superpose eq55231 eq75596
    | exact resolve eq75596 eq55231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55231 eq75596
  have eq75807 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op x y) (M.op (M.op X1 x) (M.op (M.op X0 x) (M.op (M.op x (M.op x y)) y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq75711 X0 X1
       have i₂ := eq26555 (M.op X0 x) (M.op X1 x)
       grind)
    | exact superpose eq26555 eq75711
    | exact resolve eq75711 eq26555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26555 eq75711
  have eq75880 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X1 x) (M.op (M.op X0 x) (M.op (M.op x (M.op x y)) x))) := by
    intro X0 X1
    first
    | exact superpose eq22090 eq75807
    | exact resolve eq75807 eq22090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22090 eq75807
  have eq78677 : ∀ X0 X1 : G, (k x x) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq57056 X0 X1
       grind)
    | exact superpose eq57056 eq10
    | (have j1 := eq57056 X0 X1
       grind)
    | exact resolve eq10 eq57056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78706 : ∀ X1 X2 : G, (τ (σ x)) = (k X1 (τ (σ x))) ∨ (σ (k x x)) = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq5786 x X1
       have i₂ := eq57056 x X1
       grind)
    | (have i₁ := eq5786 X1 X1
       have i₂ := eq57056 x X1
       grind)
    | exact superpose eq57056 eq5786
    | (have j1 := eq57056 X2 X1
       grind)
    | exact resolve eq5786 eq57056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57056
  have eq78852 : ∀ X1 X2 : G, x = (k X1 x) ∨ (σ (k x x)) = (M.op X2 X2) := by
    intro X1 X2
    first
    | exact superpose eq38 eq78706
    | (have j0 := eq78706 X1 X2
       grind)
    | exact resolve eq78706 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78706
  have eq79331 : ∀ X1 X2 : G, (τ (σ x)) = (k X1 (τ (σ x))) ∨ (M.op (σ (k x x)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq5786 (σ (k x x)) X1
       have i₂ := eq57057 x (σ (k x x))
       grind)
    | (have i₁ := eq5786 x X1
       have i₂ := eq57057 x (M.op x x)
       grind)
    | exact superpose eq57057 eq5786
    | (have j1 := eq57057 x X2
       grind)
    | exact resolve eq5786 eq57057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57057
  have eq79479 : ∀ X1 X2 : G, x = (k X1 x) ∨ (M.op (σ (k x x)) X2) = X2 := by
    intro X1 X2
    first
    | exact superpose eq38 eq79331
    | (have j0 := eq79331 X1 X2
       grind)
    | exact resolve eq79331 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79331
  have eq114274 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq899 (M.op X0 X0) X1 x
       have i₂ := eq944 X0 X1
       grind)
    | exact superpose eq944 eq899
    | exact resolve eq899 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114275 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq899 (M.op X0 X1) X1 x
       have i₂ := eq677 X0 X1
       grind)
    | exact superpose eq677 eq899
    | (have r₁ := eq899 (M.op (M.op X1 X1) X1) X1 x
       have r₂ := eq677 (M.op X1 X1) X1
       grind)
    | exact resolve eq899 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq114466 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114275 X0 X1 X2
       have i₂ := eq895 X0 X1 X0
       grind)
    | exact superpose eq895 eq114275
    | (have j0 := eq114275 X0 X1 X2
       grind)
    | (have r₁ := eq114275 (M.op (M.op X1 X2) (M.op X1 X2)) X1 X2
       have r₂ := eq895 X1 X2 X1
       grind)
    | (have r₁ := eq114275 (M.op x x) (M.op x X2) X2
       have r₂ := eq895 x X2 x
       grind)
    | exact resolve eq114275 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114275
  have eq114467 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114274 X0 X1 X2
       have i₂ := eq944 X1 (M.op X1 X1)
       grind)
    | exact superpose eq944 eq114274
    | (have j0 := eq114274 X0 X1 X2
       grind)
    | (have r₁ := eq114274 (M.op X0 X0) X1 X2
       have r₂ := eq944 X0 (M.op X0 X0)
       grind)
    | exact resolve eq114274 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114274
  have eq115025 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114467 X1 X2 X3
       have i₂ := eq936 X0 X1
       grind)
    | (have i₁ := eq114467 X1 X2 X3
       have i₂ := eq936 X1 X0
       grind)
    | exact superpose eq936 eq114467
    | (have j0 := eq114467 X1 X2 X3
       grind)
    | (have r₁ := eq114467 (M.op X0 X0) X1 X2
       have r₂ := eq936 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq114467 (M.op X1 X1) X1 X2
       have r₂ := eq936 (M.op X1 X1) X1
       grind)
    | exact resolve eq114467 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121033 : ∀ X1 X2 : G, (τ (σ x)) = (k X1 (τ (σ x))) ∨ (k x x) = (τ (M.op X2 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq5786 X1 X1
       have i₂ := eq78677 x X1
       grind)
    | exact superpose eq78677 eq5786
    | (have j1 := eq78677 X2 X1
       grind)
    | exact resolve eq5786 eq78677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78677
  have eq121230 : ∀ X1 X2 : G, x = (k X1 x) ∨ (k x x) = (τ (M.op X2 X2)) := by
    intro X1 X2
    first
    | exact superpose eq38 eq121033
    | (have j0 := eq121033 X1 X2
       grind)
    | exact resolve eq121033 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121033
  have eq140071 : (M.op x x) = (k (M.op (M.op x (M.op x y)) y) x) := by
    first
    | (have j0 := eq580 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq140077 : ∀ X0 : G, (M.op (σ (k x x)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq140071 eq79479
    | (have j0 := eq79479 x X0
       grind)
    | exact resolve eq79479 eq140071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79479
  have eq140078 : ∀ X0 : G, (M.op X0 X0) = (σ (k x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq140071 eq78852
    | (have j0 := eq78852 x X0
       grind)
    | exact resolve eq78852 eq140071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78852
  have eq140098 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq140077 X0
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq140077
    | (have j1 := eq14 x x
       grind)
    | exact resolve eq140077 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140077
  have eq140393 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq140098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140098
  have eq140637 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq140078 X0
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq140078
    | (have j1 := eq14 x x
       grind)
    | exact resolve eq140078 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140078
  have eq140853 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq140637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140637
  have eq141016 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq140393 X0
       have i₂ := eq936 X0 x
       grind)
    | (have i₁ := eq140393 X0
       have i₂ := eq936 x X1
       grind)
    | exact superpose eq936 eq140393
    | exact resolve eq140393 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141108 : ∀ X0 : G, (k x x) = (τ (σ (M.op x x))) ∨ x = (k X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq121230 X0 (σ (M.op x x))
       have i₂ := eq140393 (σ (M.op x x))
       grind)
    | exact superpose eq140393 eq121230
    | (have j0 := eq121230 X0 x
       grind)
    | exact resolve eq121230 eq140393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121230 eq140393
  have eq141389 : ∀ X0 : G, (k x x) = (M.op x x) ∨ x = (k X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq141108 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq141108
    | (have j0 := eq141108 X0
       grind)
    | exact resolve eq141108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141108
  have eq141460 : ∀ X0 : G, (k x x) = (M.op x x) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq141389 X0
       have j1 := eq114466 x x x
       grind)
    | (have r₁ := eq141389 X0
       have r₂ := eq114466 (k x x) x x
       grind)
    | (have r₁ := eq141389 X0
       have r₂ := eq114466 x x x
       grind)
    | exact resolve eq141389 eq114466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114466 eq141389
  have eq141501 : x = (M.op x x) ∨ (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq140071
       have i₂ := eq141460 (M.op (M.op x sF0) y)
       grind)
    | exact superpose eq141460 eq140071
    | exact resolve eq140071 eq141460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140071 eq141460
  have eq141536 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq141501
       have r₂ := eq12 x x
       grind)
    | exact resolve eq141501 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141501
  have eq143027 : (τ (M.op x x)) = (k (τ x) (τ x)) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq141536
       grind)
    | exact superpose eq141536 eq180
    | exact resolve eq180 eq141536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq143034 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ x) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq143027
       have i₂ := eq936 X0 x
       grind)
    | (have i₁ := eq143027
       have i₂ := eq936 x X0
       grind)
    | exact superpose eq936 eq143027
    | exact resolve eq143027 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143045 : ∀ X0 : G, (k (τ x) (τ x)) = (k X0 (k (τ x) (τ x))) := by
    intro X0
    first
    | (have i₁ := eq5786 x x
       have i₂ := eq143027
       grind)
    | exact superpose eq143027 eq5786
    | exact resolve eq5786 eq143027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5786 eq143027
  have eq143659 : ∀ X0 X1 : G, (σ (σ (k X0 (k (τ x) (τ x))))) = (σ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4489 X0 (M.op X1 X1)
       have i₂ := eq143034 X1
       grind)
    | exact superpose eq143034 eq4489
    | exact resolve eq4489 eq143034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq143660 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (k X0 (k (τ x) (τ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq143659 X0 X1
       have i₂ := eq1003 X1 (σ X0)
       grind)
    | exact superpose eq1003 eq143659
    | exact resolve eq143659 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq143659
  have eq143737 : ∀ X1 : G, (σ (M.op X1 X1)) = (σ (σ (k (τ x) (τ x)))) := by
    intro X1
    first
    | (have i₁ := eq143660 x X1
       have i₂ := eq143045 x
       grind)
    | exact superpose eq143045 eq143660
    | exact resolve eq143660 eq143045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143660
  have eq143771 : ∀ X1 : G, (σ (M.op X1 X1)) = (σ (k x (σ (τ x)))) := by
    intro X1
    first
    | (have i₁ := eq143737 X1
       have i₂ := eq49 x (τ x)
       grind)
    | exact superpose eq49 eq143737
    | exact resolve eq143737 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq143737
  have eq143790 : ∀ X1 : G, (σ (k x x)) = (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq143771 X1
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq143771
    | exact resolve eq143771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143771
  have eq143805 : ∀ X1 : G, (σ (M.op X1 X1)) = (σ (M.op x x)) := by
    intro X1
    first
    | (have i₁ := eq143790 X1
       have i₂ := eq141536
       grind)
    | exact superpose eq141536 eq143790
    | exact resolve eq143790 eq141536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141536 eq143790
  have eq146824 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op x x) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1535 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1535
    | (have j0 := eq1535 X1 X1
       grind)
    | exact resolve eq1535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq152775 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = X1 ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq141016 X0 X1
       have i₂ := eq143805 X0
       grind)
    | (have i₁ := eq141016 x X1
       have i₂ := eq143805 X1
       grind)
    | exact superpose eq143805 eq141016
    | (have j0 := eq141016 x X1
       grind)
    | exact resolve eq141016 eq143805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141016 eq143805
  have eq156787 : x ≠ (σ (M.op x x)) ∨ x = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have j0 := eq152775 (σ (M.op x x)) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152775
  have eq156791 : x ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq156787
       have i₂ := eq705 (σ (M.op x x))
       grind)
    | exact superpose eq705 eq156787
    | exact resolve eq156787 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156787
  have eq157117 : ∀ X0 : G, x ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq156791
       have i₂ := eq936 X0 x
       grind)
    | (have i₁ := eq156791
       have i₂ := eq936 x x
       grind)
    | exact superpose eq936 eq156791
    | exact resolve eq156791 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq156791
  have eq157766 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 (M.op X0 X1)) X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq157767 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 (M.op X0 X1)) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq157766 X0 X1
       have j1 := eq115025 X0 X0 X1 (M.op (M.op X0 (M.op X0 X1)) X1)
       grind)
    | (have r₁ := eq157766 X0 X0
       have r₂ := eq115025 X0 (k (M.op (M.op X0 (M.op X0 X0)) X0) X0) x x
       grind)
    | (have r₁ := eq157766 X1 X1
       have r₂ := eq115025 X1 X1 x x
       grind)
    | (have r₁ := eq157766 (M.op X0 X0) X1
       have r₂ := eq115025 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x x
       grind)
    | exact resolve eq157766 eq115025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115025 eq157766
  have eq158827 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op (M.op x y) X0) (M.op (M.op y x) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3077 eq157767
    | exact resolve eq157767 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq158832 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 (M.op X1 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157767 X1 X0
       have i₂ := eq2055 X1 (M.op X1 X0) X0
       grind)
    | (have i₁ := eq157767 X1 X0
       have i₂ := eq2055 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq2055 eq157767
    | exact resolve eq157767 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq158885 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1210 X1 (M.op (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) X0)) X0)
       have i₂ := eq157767 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq157767 eq1210
    | exact resolve eq1210 eq157767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq158887 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5879 X1 (M.op (M.op (σ (σ (M.op X1 X1))) (M.op (σ (σ (M.op X1 X1))) X0)) X0)
       have i₂ := eq157767 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact superpose eq157767 eq5879
    | exact resolve eq5879 eq157767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq158889 : ∀ X0 : G, (M.op X0 X0) = (k (τ x) (τ x)) := by
    intro X0
    first
    | (have i₁ := eq143045 (M.op (M.op (k (τ x) (τ x)) (M.op (k (τ x) (τ x)) X0)) X0)
       have i₂ := eq157767 (k (τ x) (τ x)) X0
       grind)
    | exact superpose eq157767 eq143045
    | exact resolve eq143045 eq157767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143045 eq157767
  have eq158936 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op y x) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq158827 x
       have i₂ := eq895 sF0 x (M.op y x)
       grind)
    | exact superpose eq895 eq158827
    | exact resolve eq158827 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158827
  have eq159166 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x (M.op (M.op y x) y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq588 eq158936
    | exact resolve eq158936 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq158936
  have eq159695 : ∀ X0 : G, x ≠ (σ (σ (M.op X0 X0))) ∨ x = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157117 X0
       have i₂ := eq158885 X0 x
       grind)
    | exact superpose eq158885 eq157117
    | exact resolve eq157117 eq158885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157117
  have eq159708 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq677 X1 X1
       have i₂ := eq158885 X1 X0
       grind)
    | exact superpose eq158885 eq677
    | exact resolve eq677 eq158885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158885
  have eq163119 : ∀ X0 : G, (M.op (k (τ x) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq677 X0 X0
       have i₂ := eq158889 X0
       grind)
    | exact superpose eq158889 eq677
    | exact resolve eq677 eq158889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158889
  have eq183941 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op x y) (M.op X0 (M.op (M.op X1 (M.op (M.op y x) X1)) X0))) (M.op y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq158832 X1 (M.op y x)
       have i₂ := eq2478 (M.op X1 (M.op (M.op y x) X1)) X0
       grind)
    | exact superpose eq2478 eq158832
    | exact resolve eq158832 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq183943 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op X1 (M.op (M.op (σ y) (σ x)) X1)) X0))) (M.op (σ y) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq2479 eq158832
    | exact resolve eq158832 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479 eq158832
  have eq183990 : ∀ X1 : G, (M.op X1 X1) = (k (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ y) (σ x)) X1) X1)) (M.op (σ y) (σ x))) := by
    intro X1
    first
    | (have i₁ := eq183943 X1 x
       have i₂ := eq3106 x X1 (M.op (M.op sF3 sF2) x)
       grind)
    | exact superpose eq3106 eq183943
    | exact resolve eq183943 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183943
  have eq183992 : ∀ X1 : G, (M.op X1 X1) = (k (M.op (M.op x y) (M.op (M.op (M.op y x) X1) X1)) (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq183941 x X1
       have i₂ := eq3106 X1 x (M.op (M.op y x) X1)
       grind)
    | exact superpose eq3106 eq183941
    | exact resolve eq183941 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183941
  have eq184180 : ∀ X1 : G, (M.op X1 X1) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) (M.op (σ y) (σ x))) := by
    intro X1
    first
    | (have i₁ := eq183990 X1
       have i₂ := eq677 (M.op sF3 sF2) X1
       grind)
    | exact superpose eq677 eq183990
    | exact resolve eq183990 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183990
  have eq184182 : ∀ X1 : G, (M.op X1 X1) = (k (M.op (M.op x y) (M.op y x)) (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq183992 X1
       have i₂ := eq677 (M.op y x) X1
       grind)
    | exact superpose eq677 eq183992
    | exact resolve eq183992 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183992
  have eq184287 : ∀ X1 : G, (M.op X1 X1) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ y) (σ x))) := by
    intro X1
    first
    | (have i₁ := eq184180 X1
       have i₂ := eq688 sF4 sF2 sF3
       grind)
    | (have i₁ := eq184180 X1
       have i₂ := eq688 sF3 sF2 sF4
       grind)
    | exact superpose eq688 eq184180
    | exact resolve eq184180 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184180
  have eq184289 : ∀ X1 : G, (M.op X1 X1) = (k (M.op y (M.op (M.op x y) x)) (M.op y x)) := by
    intro X1
    first
    | (have i₁ := eq184182 X1
       have i₂ := eq688 sF0 x y
       grind)
    | (have i₁ := eq184182 X1
       have i₂ := eq688 y x sF0
       grind)
    | exact superpose eq688 eq184182
    | exact resolve eq184182 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq184182
  have eq193136 : (k (τ x) (τ x)) = (k (M.op x (M.op (M.op y x) y)) (M.op x y)) := by
    first
    | (have i₁ := eq163119 (k (τ x) (τ x))
       have i₂ := eq159166 (k (τ x) (τ x))
       grind)
    | exact superpose eq159166 eq163119
    | exact resolve eq163119 eq159166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163119
  have eq193144 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op x (M.op (M.op y x) y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq143034 X0
       have i₂ := eq193136
       grind)
    | exact superpose eq193136 eq143034
    | exact resolve eq143034 eq193136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143034 eq193136
  have eq200586 : (k (M.op x (M.op (M.op y x) y)) (M.op x y)) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq159166 x
       have i₂ := eq184287 x
       grind)
    | exact superpose eq184287 eq159166
    | exact resolve eq159166 eq184287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159166
  have eq200898 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq200586 eq193144
    | exact resolve eq193144 eq200586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193144 eq200586
  have eq201381 : (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ y) (σ x))) = (k (M.op y (M.op (M.op x y) x)) (M.op y x)) := by
    first
    | (have i₁ := eq184287 x
       have i₂ := eq184289 x
       grind)
    | exact superpose eq184289 eq184287
    | exact resolve eq184287 eq184289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184287
  have eq201398 : ∀ X0 : G, (M.op (k (M.op y (M.op (M.op x y) x)) (M.op y x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq677 X0 X0
       have i₂ := eq184289 X0
       grind)
    | exact superpose eq184289 eq677
    | exact resolve eq677 eq184289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184289
  have eq201646 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op y (M.op (M.op x y) x)) (M.op y x)) := by
    intro X0
    first
    | exact superpose eq201381 eq200898
    | exact resolve eq200898 eq201381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200898 eq201381
  have eq222991 : ∀ X0 X1 : G, (M.op X0 X0) ≠ x ∨ x = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq159695 X1
       have i₂ := eq158887 X0 X1
       grind)
    | exact superpose eq158887 eq159695
    | (have j0 := eq159695 X1
       grind)
    | exact resolve eq159695 eq158887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158887 eq159695
  have eq228744 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1473 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1473
    | (have j0 := eq1473 x y
       grind)
    | exact resolve eq1473 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq228793 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq228744
    | exact resolve eq228744 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228744
  have eq228794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228793
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228793
    | exact resolve eq228793 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228793
  have eq228795 : (σ (M.op x y)) = (M.op (M.op (σ y) x) (M.op (σ x) x)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228794
       have i₂ := eq749 sF3 (σ x)
       grind)
    | exact superpose eq749 eq228794
    | exact resolve eq228794 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228794
  have eq228796 : (σ (M.op x y)) = (M.op (M.op (σ y) x) (M.op (σ x) x)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228795
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228795
    | exact resolve eq228795 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228795
  have eq228797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228796
       have i₂ := eq749 sF3 sF2
       grind)
    | exact superpose eq749 eq228796
    | exact resolve eq228796 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228796
  have eq228798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq228797
    | exact resolve eq228797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228797
  have eq228799 : (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq228798
       have r₂ := eq27
       grind)
    | exact resolve eq228798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228798
  have eq228800 : (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228799
    | exact resolve eq228799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228799
  have eq228801 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228800
    | exact resolve eq228800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228800
  have eq228802 : (σ x) = (M.op (M.op (σ y) x) (M.op (σ x) x)) ∨ (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228801
       have i₂ := eq749 sF3 (σ x)
       grind)
    | exact superpose eq749 eq228801
    | exact resolve eq228801 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228801
  have eq228803 : (σ x) = (M.op (M.op (σ y) x) (M.op (σ x) x)) ∨ (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228802
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228802
    | exact resolve eq228802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228802
  have eq228804 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq228803
       have i₂ := eq749 sF3 sF2
       grind)
    | exact superpose eq749 eq228803
    | exact resolve eq228803 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228803
  have eq228805 : (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq228804
    | exact resolve eq228804 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228804
  have eq228874 : (σ x) = (σ (σ x)) ∨ x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq140853 x
       have i₂ := eq228805
       grind)
    | exact superpose eq228805 eq140853
    | exact resolve eq140853 eq228805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140853
  have eq229061 : x ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq228805
  have eq229106 : (σ x) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq228874
       have r₂ := eq229061
       grind)
    | exact resolve eq228874 eq229061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228874
  have eq229129 : (σ x) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq229106 eq10
    | exact resolve eq10 eq229106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229106
  have eq229168 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq229129
    | exact resolve eq229129 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229129
  have eq229173 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq229168
       have r₂ := eq229061
       grind)
    | exact resolve eq229168 eq229061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229061 eq229168
  have eq229221 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq944 x X0
       have i₂ := eq229173
       grind)
    | exact superpose eq229173 eq944
    | exact resolve eq944 eq229173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229281 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq159708 x X0
       have i₂ := eq229173
       grind)
    | exact superpose eq229173 eq159708
    | exact resolve eq159708 eq229173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229173
  have eq229516 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq229281 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq229281
    | (have j0 := eq229281 X0
       grind)
    | exact resolve eq229281 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229281
  have eq229696 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq229221 y
       grind)
    | exact superpose eq229221 eq18
    | (have j1 := eq229221 y
       grind)
    | exact resolve eq18 eq229221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229221
  have eq230247 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq229696 eq889
    | exact resolve eq889 eq229696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229696
  have eq230562 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X1 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229516 eq114467
    | (have j0 := eq114467 (σ x) X0 X1
       grind)
    | (have r₁ := eq114467 (σ x) X1 x
       have r₂ := eq229516 (σ x)
       grind)
    | exact resolve eq114467 eq229516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114467 eq229516
  have eq230923 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq230562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230562
  have eq269928 : ∀ X0 : G, (M.op y x) = (M.op (M.op x y) (k X0 (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1122 x
       have i₂ := eq230923 x X0
       grind)
    | exact superpose eq230923 eq1122
    | exact resolve eq1122 eq230923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230923
  have eq601053 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq230247 eq8332
    | exact resolve eq8332 eq230247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8332 eq230247
  have eq601170 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq601053 x
       have i₂ := eq944 sF2 x
       grind)
    | exact superpose eq944 eq601053
    | exact resolve eq601053 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601053
  have eq602410 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op X0 X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq601170 (σ (M.op X0 X0))
       have i₂ := eq159708 X0 sF4
       grind)
    | exact superpose eq159708 eq601170
    | exact resolve eq601170 eq159708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601170
  have eq606424 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq602410 X0
       grind)
    | exact superpose eq602410 eq10
    | exact resolve eq10 eq602410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602410
  have eq607644 : (M.op y x) = (M.op (M.op x y) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1122 x
       have i₂ := eq606424 x
       grind)
    | exact superpose eq606424 eq1122
    | exact resolve eq1122 eq606424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq606424
  have eq631869 : ∀ X0 : G, (M.op x y) = (M.op (M.op y x) (k X0 (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq269928 eq677
    | exact resolve eq677 eq269928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269928
  have eq680800 : (M.op x y) = (M.op (M.op y x) (σ (k y x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61 eq631869
    | exact resolve eq631869 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq631869
  have eq1093679 : (σ (k y x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2432 x y (σ (k y x))
       have i₂ := eq680800
       grind)
    | exact superpose eq680800 eq2432
    | exact resolve eq2432 eq680800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432 eq680800
  have eq1093683 : (σ (k y x)) = (M.op (M.op x y) (M.op (M.op x x) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1093679
       have i₂ := eq3094 x sF0
       grind)
    | exact superpose eq3094 eq1093679
    | exact resolve eq1093679 eq3094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093679
  have eq1093687 : (σ (k y x)) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1093683
       have i₂ := eq3106 x sF0 x
       grind)
    | exact superpose eq3106 eq1093683
    | exact resolve eq1093683 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093683
  have eq1093688 : (σ (k y x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1093687
       have r₂ := eq7046
       grind)
    | exact resolve eq1093687 eq7046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046 eq1093687
  have eq1093936 : (k y x) = (τ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1093688
       grind)
    | exact superpose eq1093688 eq10
    | exact resolve eq10 eq1093688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093688
  have eq1094201 : (k y x) = (k (M.op y (M.op (M.op x y) x)) (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1093936
       have i₂ := eq201646 x
       grind)
    | exact superpose eq201646 eq1093936
    | exact resolve eq1093936 eq201646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201646 eq1093936
  have eq1145230 : (M.op x y) = (M.op (M.op y x) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq607644 eq677
    | exact resolve eq677 eq607644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607644
  have eq1166634 : ∀ X0 : G, (M.op (k y x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1094201 eq201398
    | exact resolve eq201398 eq1094201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201398 eq1094201
  have eq1166901 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq705 (k y x)
       have i₂ := eq1166634 (k y x)
       grind)
    | exact superpose eq1166634 eq705
    | exact resolve eq705 eq1166634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166634
  have eq1168332 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq1166901
       have r₂ := eq850
       grind)
    | exact resolve eq1166901 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq1166901
  have eq1168407 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) := by
    first
    | (have i₁ := eq780
       have i₂ := eq1168332
       grind)
    | exact superpose eq1168332 eq780
    | exact resolve eq780 eq1168332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq1170069 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146824 y x
       have i₂ := eq1168332
       grind)
    | exact superpose eq1168332 eq146824
    | (have j0 := eq146824 x x
       grind)
    | exact resolve eq146824 eq1168332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146824 eq1168332
  have eq1170070 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1170069
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1170069
    | exact resolve eq1170069 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170069
  have eq1170151 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1170070
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1170070
    | exact resolve eq1170070 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170070
  have eq1170674 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq944 x X0
       have i₂ := eq1170151
       grind)
    | exact superpose eq1170151 eq944
    | exact resolve eq944 eq1170151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170151
  have eq1171261 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1170674 eq674
    | exact resolve eq674 eq1170674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq1170674
  have eq1171605 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq944 x X0
       have i₂ := eq1171261
       grind)
    | exact superpose eq1171261 eq944
    | exact resolve eq944 eq1171261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171665 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq159708 x X0
       have i₂ := eq1171261
       grind)
    | exact superpose eq1171261 eq159708
    | exact resolve eq159708 eq1171261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171261
  have eq1172041 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1171665 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1171665
    | (have j0 := eq1171665 X0
       grind)
    | exact resolve eq1171665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171665
  have eq1172177 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq159708 x X0
       have i₂ := eq1168407
       grind)
    | exact superpose eq1168407 eq159708
    | exact resolve eq159708 eq1168407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168407
  have eq1174888 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1171605 y
       grind)
    | exact superpose eq1171605 eq18
    | (have j1 := eq1171605 y
       grind)
    | exact resolve eq18 eq1171605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171605
  have eq1176186 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1174888 eq20
    | exact resolve eq20 eq1174888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174888
  have eq1176233 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1176186
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1176186
    | exact resolve eq1176186 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176186
  have eq1179858 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1172041 eq26
    | (have j1 := eq1172041 (σ y)
       grind)
    | exact resolve eq26 eq1172041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172041
  have eq1180957 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1179858 eq27
    | exact resolve eq27 eq1179858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179858
  have eq1180983 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1180957
       have r₂ := eq1176233
       grind)
    | exact resolve eq1180957 eq1176233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176233 eq1180957
  have eq1180985 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1180983 eq20
    | exact resolve eq20 eq1180983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180990 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1180983 eq601
    | exact resolve eq601 eq1180983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq1181105 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1180985
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1180985
    | exact resolve eq1180985 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180985
  have eq1181107 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1181105 eq26
    | exact resolve eq26 eq1181105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182659 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ (M.op x y))) (σ y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq1181107 eq894
    | exact resolve eq894 eq1181107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1182661 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1181107 eq895
    | exact resolve eq895 eq1181107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182662 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1181107 eq895
    | exact resolve eq895 eq1181107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq1181107
  have eq1182779 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3101 eq1182662
    | exact resolve eq1182662 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101 eq1182662
  have eq1182780 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq889 eq1182661
    | exact resolve eq1182661 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182661
  have eq1182782 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq889 eq1182659
    | exact resolve eq1182659 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq1182659
  have eq1182820 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1182779 X0
       have i₂ := eq3106 X0 sF4 sF2
       grind)
    | exact superpose eq3106 eq1182779
    | exact resolve eq1182779 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106 eq1182779
  have eq1184115 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq1182780 eq677
    | exact resolve eq677 eq1182780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182780
  have eq1184821 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (σ (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1182782 (σ (M.op X0 X0))
       have i₂ := eq159708 X0 sF1
       grind)
    | exact superpose eq159708 eq1182782
    | exact resolve eq1182782 eq159708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159708
  have eq1184997 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1182782 eq770
    | exact resolve eq770 eq1182782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq1182782
  have eq1198217 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1184821 X0
       grind)
    | exact superpose eq1184821 eq10
    | exact resolve eq10 eq1184821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184821
  have eq1201545 : (M.op (σ (M.op x y)) (σ x)) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1184997 x
       have i₂ := eq1198217 x
       grind)
    | exact superpose eq1198217 eq1184997
    | exact resolve eq1184997 eq1198217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184997 eq1198217
  have eq1201692 : (M.op (σ (M.op x y)) (σ x)) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ x = y := by grind
  clear eq1201545
  have eq1209382 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 y) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1180990 (M.op X0 y)
       have i₂ := eq677 X0 y
       grind)
    | exact superpose eq677 eq1180990
    | exact resolve eq1180990 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209566 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op x x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7838 x x
       have i₂ := eq1180990 (M.op x sF0)
       grind)
    | exact superpose eq1180990 eq7838
    | exact resolve eq7838 eq1180990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838 eq1180990
  have eq1209703 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1209566 X0
       have i₂ := eq944 x X0
       grind)
    | exact superpose eq944 eq1209566
    | exact resolve eq1209566 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209566
  have eq1209759 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op (M.op X0 x) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1209382 X0
       have i₂ := eq3094 X0 x
       grind)
    | exact superpose eq3094 eq1209382
    | exact resolve eq1209382 eq3094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094 eq1209382
  have eq1209802 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1209759 X0
       have i₂ := eq677 X0 x
       grind)
    | exact superpose eq677 eq1209759
    | exact resolve eq1209759 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209759
  have eq1211686 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op x y)) x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1182820 eq1209703
    | exact resolve eq1209703 eq1182820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182820 eq1209703
  have eq1211843 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op x y)) x) ∨ x = y := by grind
  clear eq1211686
  have eq1211919 : (σ x) = (M.op (M.op x x) (M.op (M.op (σ (M.op x y)) x) (M.op (M.op x (M.op x y)) x))) ∨ x = y := by
    first
    | exact superpose eq75880 eq1211843
    | exact resolve eq1211843 eq75880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75880 eq1211843
  have eq1211964 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op (M.op x (M.op x y)) x)) ∨ x = y := by
    first
    | (have i₁ := eq1211919
       have i₂ := eq2833 (M.op x sF0) x (M.op sF1 x)
       grind)
    | exact superpose eq2833 eq1211919
    | exact resolve eq1211919 eq2833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833 eq1211919
  have eq1211992 : (σ x) = (M.op (M.op x (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1211964
       have i₂ := eq749 sF1 (M.op x sF0)
       grind)
    | exact superpose eq749 eq1211964
    | exact resolve eq1211964 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq1211964
  have eq1220327 : (M.op x y) = (M.op (M.op x (σ x)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1209802 eq1184115
    | exact resolve eq1184115 eq1209802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184115 eq1209802
  have eq1220364 : (M.op x y) = (M.op (M.op x (σ x)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq1220327
  have eq1226397 : (M.op (M.op x (M.op x y)) (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op y x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq1211992 eq3121
    | exact resolve eq3121 eq1211992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121 eq1211992
  have eq1226451 : x = (M.op (σ (M.op x y)) (M.op (M.op y x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq1226397
       have i₂ := eq677 x sF0
       grind)
    | exact superpose eq677 eq1226397
    | exact resolve eq1226397 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq1226397
  have eq1428529 : (σ x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1172177 eq665
    | exact resolve eq665 eq1172177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172177
  have eq1428778 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq944 x X0
       have i₂ := eq1428529
       grind)
    | exact superpose eq1428529 eq944
    | exact resolve eq944 eq1428529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428529
  have eq1429067 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1181105 eq1428778
    | exact resolve eq1428778 eq1181105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181105 eq1428778
  have eq1430108 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1429067 X0
       grind)
    | (have r₁ := eq1429067 X0
       have r₂ := eq27
       grind)
    | exact resolve eq1429067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429067
  have eq1435848 : (σ x) = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1430108 eq1201692
    | exact resolve eq1201692 eq1430108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201692
  have eq1436334 : (σ x) = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1435848
  have eq1436473 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq38 eq1436334
    | exact resolve eq1436334 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436334
  have eq1436575 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq1436473 eq39
    | exact resolve eq39 eq1436473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436473
  have eq1436617 : x = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq1436575
    | exact resolve eq1436575 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436575
  have eq1436706 : (M.op x y) = (M.op (M.op x x) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1436617 eq1220364
    | exact resolve eq1220364 eq1436617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220364 eq1436617
  have eq1436760 : (M.op x y) = (M.op (M.op x x) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1436706
  have eq1436818 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1436760
       have i₂ := eq944 x sF1
       grind)
    | exact superpose eq944 eq1436760
    | exact resolve eq1436760 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436760
  have eq1436950 : (M.op x y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1436818 eq37
    | exact resolve eq37 eq1436818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436818
  have eq1440734 : x = (τ x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1180983 eq1436950
    | exact resolve eq1436950 eq1180983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436950
  have eq1440746 : x = (τ x) ∨ x = y := by grind
  clear eq1440734
  have eq1441169 : x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq11 x
       have i₂ := eq1440746
       grind)
    | exact superpose eq1440746 eq11
    | exact resolve eq11 eq1440746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440746
  have eq1441215 : x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1441169
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1441169
    | exact resolve eq1441169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441169
  have eq1441580 : x = (M.op (σ (M.op x y)) (M.op (M.op y x) x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1441215 eq1226451
    | exact resolve eq1226451 eq1441215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226451 eq1441215
  have eq1441796 : x = (M.op (σ (M.op x y)) (M.op (M.op y x) x)) ∨ x = y := by grind
  clear eq1441580
  have eq1441899 : x = (M.op (M.op x x) (M.op (σ (M.op x y)) y)) ∨ x = y := by
    first
    | (have i₁ := eq1441796
       have i₂ := eq3621 y x x sF1
       grind)
    | exact superpose eq3621 eq1441796
    | exact resolve eq1441796 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq1441796
  have eq1441908 : x = (M.op (σ (M.op x y)) y) ∨ x = y := by
    first
    | (have i₁ := eq1441899
       have i₂ := eq944 x (M.op sF1 y)
       grind)
    | exact superpose eq944 eq1441899
    | exact resolve eq1441899 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441899
  have eq1446415 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1441908 eq1430108
    | exact resolve eq1430108 eq1441908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430108 eq1441908
  have eq1446496 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1446415
  have eq1446577 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1446496 eq39
    | exact resolve eq39 eq1446496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1446496
  have eq1446704 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq1446577
    | exact resolve eq1446577 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1446577
  have eq1446838 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1446704 eq1180983
    | exact resolve eq1180983 eq1446704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180983 eq1446704
  have eq1447241 : x = y := by grind
  clear eq1446838
  have eq1447365 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1447241
       grind)
    | exact superpose eq1447241 eq18
    | exact resolve eq18 eq1447241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1447366 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1447241
       grind)
    | exact superpose eq1447241 eq24
    | exact resolve eq24 eq1447241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1458952 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op y x) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1145230
       have i₂ := eq1447241
       grind)
    | exact superpose eq1447241 eq1145230
    | exact resolve eq1145230 eq1447241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145230
  have eq1459993 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op y x) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) := by grind
  clear eq1458952
  have eq1461323 : (M.op x y) = (M.op (M.op x x) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1459993
       have i₂ := eq1447241
       grind)
    | exact superpose eq1447241 eq1459993
    | exact resolve eq1459993 eq1447241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447241 eq1459993
  have eq1464267 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1447366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1447366
    | exact resolve eq1447366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1447366
  have eq1464273 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq705 X0
       have i₂ := eq1447365
       grind)
    | exact superpose eq1447365 eq705
    | exact resolve eq705 eq1447365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq1447365
  have eq1468134 : (M.op x y) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1461323
       have i₂ := eq944 x (τ (M.op sF4 sF2))
       grind)
    | exact superpose eq944 eq1461323
    | exact resolve eq1461323 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq1461323
  have eq1471526 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1464267 eq26
    | exact resolve eq26 eq1464267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1471527 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1464267 eq665
    | exact resolve eq665 eq1464267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq1464267
  have eq1477978 : ∀ X1 : G, x ≠ (M.op x y) ∨ x = (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq222991 x X1
       have i₂ := eq1464273 x
       grind)
    | exact superpose eq1464273 eq222991
    | (have j0 := eq222991 x X1
       grind)
    | exact resolve eq222991 eq1464273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222991
  have eq1482879 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1471527 eq1468134
    | exact resolve eq1468134 eq1471527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468134 eq1471527
  have eq1482946 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1471526
       have i₂ := eq1464273 sF2
       grind)
    | exact superpose eq1464273 eq1471526
    | exact resolve eq1471526 eq1464273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471526
  have eq1485281 : x = (σ (M.op x y)) ∨ x ≠ (M.op x y) := by
    first
    | (have i₁ := eq1477978 x
       have i₂ := eq1464273 x
       grind)
    | exact superpose eq1464273 eq1477978
    | exact resolve eq1477978 eq1464273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464273 eq1477978
  have eq1489479 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq1482879
    | exact resolve eq1482879 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1482879
  have eq1489480 : x = (M.op x y) := by grind
  clear eq1489479
  have eq1489632 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1482946 eq27
    | exact resolve eq27 eq1482946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1482946
  have eq1500814 : x = (σ (M.op x y)) ∨ x ≠ (M.op x y) := by
    first
    | exact superpose eq20 eq1485281
    | exact resolve eq1485281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1485281
  have eq1505040 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1489480 eq1489632
    | exact resolve eq1489632 eq1489480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489632
  have eq1506189 : x = (σ (M.op x y)) := by
    first
    | (have r₁ := eq1500814
       have r₂ := eq1489480
       grind)
    | exact resolve eq1500814 eq1489480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489480 eq1500814
  have eq1509046 : False := by grind
  exact eq1509046

/-- `Equation1912`: `x = (y ◇ (x ◇ z)) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pyx_pyy_pxy_Equation1912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X2 X0)) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq177 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq16 X2 (M.op x (M.op X0 X2)) X0
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op X1 (M.op X0 X2)) (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op x (M.op x y)) := by
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
  have eq184 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X2 X0)
       have i₂ := eq177 X2 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ y) (σ x))))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq381 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq465 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq381
    | exact resolve eq381 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq612 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (k X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k X0 (M.op X0 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq177 X0 X0
       grind)
    | (have i₁ := eq613 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq613
    | exact resolve eq613 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq628 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq177 X0 X0
       grind)
    | (have i₁ := eq612 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq612
    | exact resolve eq612 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq629 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X1 X2 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq182
    | exact resolve eq182 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (k X0 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op X0 X0) X1 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 (M.op X0 X0))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq177 X0 X0
       grind)
    | (have i₁ := eq630 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq177 eq630
    | exact resolve eq630 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq692 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 X1 : G, (M.op (k X0 (M.op X0 X0)) (M.op (M.op X1 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 (M.op X0 X0) X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq187
    | exact resolve eq187 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq187
    | (have j0 := eq187 y x X0
       grind)
    | exact resolve eq187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, (M.op y (M.op (M.op X0 (M.op x y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq187
    | exact resolve eq187 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq187
    | (have j0 := eq187 (σ y) (σ x) X0
       grind)
    | exact resolve eq187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq855 : y = (M.op (M.op x y) (k y (M.op y y))) := by
    first
    | (have i₁ := eq790 y
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq790
    | exact resolve eq790 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq790 eq177
    | exact resolve eq177 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq899 : ∀ X0 : G, (M.op y X0) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq791 eq177
    | exact resolve eq177 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq923 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq792 sF3
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq792
    | exact resolve eq792 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq792 eq177
    | exact resolve eq177 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq992 : (k y (M.op y y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq855 eq177
    | exact resolve eq177 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq1021 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op (M.op x y) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 y X1 X0
       have i₂ := eq865 X0
       grind)
    | (have i₁ := eq187 y X1 x
       have i₂ := eq865 x
       grind)
    | exact superpose eq865 eq187
    | exact resolve eq187 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1100 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq899 eq182
    | exact resolve eq182 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq899
  have eq1122 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq177 X0 sF0
       grind)
    | (have i₁ := eq1100 X0 X1
       have i₂ := eq177 X0 (M.op X0 (M.op X0 sF0))
       grind)
    | exact superpose eq177 eq1100
    | exact resolve eq1100 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1134 : (k (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq923 eq177
    | exact resolve eq177 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1165 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq933 eq187
    | exact resolve eq187 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1280 : (k (σ y) (σ (M.op y y))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq36
    | exact resolve eq36 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq992
  have eq1307 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | exact superpose eq1021 eq177
    | exact resolve eq177 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1445 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq1165 eq177
    | exact resolve eq177 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1779 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq724
       grind)
    | exact superpose eq724 eq40
    | exact resolve eq40 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq1780 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1779
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1779
    | exact resolve eq1779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1782 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1780
    | exact resolve eq1780 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq2179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq629 X1 X2 X3
       have i₂ := eq629 X1 X2 X0
       grind)
    | (have i₁ := eq629 X0 X1 X2
       have i₂ := eq629 X0 X1 X1
       grind)
    | exact superpose eq629 eq629
    | exact resolve eq629 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2211 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (k X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1 (M.op X0 X0)
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq629
    | exact resolve eq629 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2326 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op X2 X1) X2
       have i₂ := eq629 X1 X2 X0
       grind)
    | (have i₁ := eq177 (M.op X2 X0) X1
       have i₂ := eq629 X0 X1 X2
       grind)
    | exact superpose eq629 eq177
    | exact resolve eq177 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq3243 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2179 X1 (M.op X2 X0) X3 (M.op x (M.op X0 X2))
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq2179
    | exact resolve eq2179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq16163 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq692 X0 X0 (M.op x (k X0 (M.op X0 X0)))
       have i₂ := eq667 X0 x
       grind)
    | exact superpose eq667 eq692
    | (have j0 := eq692 X0 X0 x
       grind)
    | exact resolve eq692 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq692
  have eq16203 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163
  have eq16294 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 (k X0 X0)
       have i₂ := eq16203 X0
       grind)
    | exact superpose eq16203 eq177
    | (have j1 := eq16203 X0
       grind)
    | exact resolve eq177 eq16203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16203
  have eq16414 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16294 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16294 X0
       have r₂ := eq13 X0 (k X0 X0)
       grind)
    | (have r₁ := eq16294 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq16294 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq16294 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294
  have eq16517 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 (k X0 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq16414 X0
       grind)
    | exact superpose eq16414 eq627
    | exact resolve eq627 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq16518 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq16414 X0
       grind)
    | exact superpose eq16414 eq628
    | exact resolve eq628 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq16526 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0
       have i₂ := eq16414 X0
       grind)
    | exact superpose eq16414 eq177
    | exact resolve eq177 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq16573 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op y X0) (M.op y X0)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1122 X0 (M.op y X0)
       have i₂ := eq16414 (M.op y X0)
       grind)
    | exact superpose eq16414 eq1122
    | exact resolve eq1122 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq16610 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k y y) X0) := by
    intro X0
    first
    | (have i₁ := eq1307 X0 y
       have i₂ := eq16414 y
       grind)
    | exact superpose eq16414 eq1307
    | exact resolve eq1307 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq16668 : (σ (M.op (M.op x y) y)) = (k (σ y) (σ (k y y))) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq16414 y
       grind)
    | exact superpose eq16414 eq1280
    | exact resolve eq1280 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq16695 : (k (σ y) (k (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq1134
       have i₂ := eq16414 sF3
       grind)
    | exact superpose eq16414 eq1134
    | exact resolve eq1134 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq16734 : (σ (M.op (M.op x y) y)) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16668
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq16668
    | exact resolve eq16668 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16668
  have eq16816 : (k (σ y) (k (σ y) (σ y))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq16734
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16734
    | exact resolve eq16734 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16734
  have eq16823 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16695 eq16816
    | exact resolve eq16816 eq16695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16695 eq16816
  have eq16824 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16526 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16526
    | exact resolve eq16526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16825 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16526 (τ X0)
       have i₂ := eq465 X0 X0
       grind)
    | exact superpose eq465 eq16526
    | exact resolve eq16526 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq19012 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 (k X0 X0))) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2326 (M.op x X0) (k X0 (k X0 X0)) X1
       have i₂ := eq16518 X0 x
       grind)
    | exact superpose eq16518 eq2326
    | exact resolve eq2326 eq16518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326 eq16518
  have eq134768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1782 eq730
    | exact resolve eq730 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq1782
  have eq134781 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq134768
       have r₂ := eq27
       grind)
    | exact resolve eq134768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134768
  have eq134790 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq134781
       have i₂ := eq16414 sF2
       grind)
    | exact superpose eq16414 eq134781
    | exact resolve eq134781 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134781
  have eq134797 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq134790
       have i₂ := eq16414 x
       grind)
    | exact superpose eq16414 eq134790
    | exact resolve eq134790 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16414 eq134790
  have eq135597 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq134797 eq97
    | exact resolve eq97 eq134797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq134797
  have eq135698 : y = (k x x) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq135597
    | exact resolve eq135597 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135597
  have eq135699 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq135698
  have eq135802 : (σ x) = (M.op (M.op (σ x) (k (σ y) (k (σ y) (σ y)))) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq135699 eq19012
    | exact resolve eq19012 eq135699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135699
  have eq135821 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq135802
       have i₂ := eq16517 sF3 sF2
       grind)
    | exact superpose eq16517 eq135802
    | exact resolve eq135802 eq16517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135802
  have eq136328 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq135821 eq16825
    | exact resolve eq16825 eq135821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16825 eq135821
  have eq136390 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq136328
    | exact resolve eq136328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq136328
  have eq136436 : y = (M.op y x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq136390
    | exact resolve eq136390 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq136390
  have eq136437 : y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq136436
  have eq136474 : x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16526 x
       have i₂ := eq136437
       grind)
    | exact superpose eq136437 eq16526
    | exact resolve eq16526 eq136437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16526 eq136437
  have eq136563 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136474
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136474
    | exact resolve eq136474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136474
  have eq136650 : (M.op x y) = (M.op (k y y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16573 x
       have i₂ := eq136563
       grind)
    | exact superpose eq136563 eq16573
    | exact resolve eq16573 eq136563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq136701 : x = (M.op (M.op x (k y (k y y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19012 y x
       have i₂ := eq136563
       grind)
    | exact superpose eq136563 eq19012
    | exact resolve eq19012 eq136563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19012 eq136563
  have eq136720 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136701
       have i₂ := eq16517 y x
       grind)
    | exact superpose eq16517 eq136701
    | exact resolve eq136701 eq16517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16517 eq136701
  have eq136764 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136650
       have i₂ := eq16610 (M.op x sF0)
       grind)
    | exact superpose eq16610 eq136650
    | exact resolve eq136650 eq16610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16610 eq136650
  have eq136806 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq183 eq136764
    | exact resolve eq136764 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq136764
  have eq137093 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16824 y
       have i₂ := eq136720
       grind)
    | exact superpose eq136720 eq16824
    | exact resolve eq16824 eq136720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16824 eq136720
  have eq137163 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137093
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137093
    | exact resolve eq137093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137093
  have eq137205 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137163
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq137163
    | exact resolve eq137163 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq137163
  have eq137247 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq136806 eq16823
    | exact resolve eq16823 eq136806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136806
  have eq137378 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq137247
    | exact resolve eq137247 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137247
  have eq138195 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq137205 eq217
    | exact resolve eq217 eq137205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq137205
  have eq138339 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq138195 X1 X1
       have i₂ := eq3243 (M.op X1 sF3) X1 sF4 sF3
       grind)
    | exact superpose eq3243 eq138195
    | exact resolve eq138195 eq3243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243 eq138195
  have eq138373 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1445 eq138339
    | (have j0 := eq138339 (σ x)
       grind)
    | exact resolve eq138339 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq138339
  have eq138387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137378 eq138373
    | exact resolve eq138373 eq137378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137378 eq138373
  have eq138393 : x = (M.op x y) := by
    first
    | (have r₁ := eq138387
       have r₂ := eq27
       grind)
    | exact resolve eq138387 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138387
  have eq138398 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq138393
       grind)
    | exact superpose eq138393 eq18
    | exact resolve eq18 eq138393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq138399 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq138393
       grind)
    | exact superpose eq138393 eq22
    | exact resolve eq22 eq138393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq138393
  have eq138473 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq138399 eq20
    | exact resolve eq20 eq138399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138399
  have eq139084 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq138398 eq16823
    | exact resolve eq16823 eq138398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16823 eq138398
  have eq139215 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20 eq139084
    | exact resolve eq139084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq139084
  have eq139242 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq138473 eq139215
    | exact resolve eq139215 eq138473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139215
  have eq139546 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (M.op (σ y) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq139242 eq774
    | exact resolve eq774 eq139242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq139617 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (M.op (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq184 eq139546
    | exact resolve eq139546 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq139546
  have eq139679 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq139617
       have i₂ := eq2211 sF3 sF3
       grind)
    | exact superpose eq2211 eq139617
    | exact resolve eq139617 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211 eq139617
  have eq139696 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq933 eq139679
    | exact resolve eq139679 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq139679
  have eq139702 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139242 eq139696
    | exact resolve eq139696 eq139242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139242 eq139696
  have eq139705 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq139702 eq27
    | exact resolve eq27 eq139702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq139702
  have eq140005 : False := by grind
  exact eq140005

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq87
  have eq195 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq198 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq198 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq198 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq216 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq203 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq203 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq203
  have eq226 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq216
    | (have j0 := eq216 X0 X1
       grind)
    | exact resolve eq216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq233 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227
    | exact resolve eq227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq227 x y
       grind)
    | exact superpose eq227 eq16
    | exact resolve eq16 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq314 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq233 X0 (τ X1)
       grind)
    | exact superpose eq233 eq18
    | exact resolve eq18 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq233
  have eq329 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq314
    | exact resolve eq314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq336 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq329
    | exact resolve eq329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq348 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq244
       have i₂ := eq336 x y
       grind)
    | exact superpose eq336 eq244
    | exact resolve eq244 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq336
  have eq349 : False := by grind
  exact eq349
