import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq138 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128 y x
       grind)
    | exact superpose eq128 eq16
    | (have j1 := eq128 y x
       grind)
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq154 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq26
    | exact resolve eq26 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq327 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq154 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq154
    | exact resolve eq154 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq362 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq327 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq372 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq362 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq362
    | exact resolve eq362 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq375 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq372
    | exact resolve eq372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq405 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq375 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq375
    | exact resolve eq375 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq487 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq405 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq405
    | exact resolve eq405 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq138
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq138
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq138 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq741 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq740
  have eq13653 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq741
       grind)
    | exact superpose eq741 eq16
    | exact resolve eq16 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq13654 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq13653
       have r₂ := eq23 x
       grind)
    | exact resolve eq13653 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13653
  have eq128240 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13654
       grind)
    | exact superpose eq13654 eq10
    | exact resolve eq10 eq13654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13654
  have eq128505 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq128240
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128240
    | exact resolve eq128240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128240
  have eq130557 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128505
       grind)
    | exact superpose eq128505 eq16
    | exact resolve eq16 eq128505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128505
  have eq130558 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq130557
       have r₂ := eq23 x
       grind)
    | exact resolve eq130557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq130557
  have eq130562 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq130558
       grind)
    | exact superpose eq130558 eq26
    | exact resolve eq26 eq130558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130704 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq130558
       grind)
    | exact superpose eq130558 eq64
    | exact resolve eq64 eq130558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq130558
  have eq131775 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq405 y
       have i₂ := eq130704
       grind)
    | exact superpose eq130704 eq405
    | exact resolve eq405 eq130704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq130704
  have eq177004 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131775
       grind)
    | exact superpose eq131775 eq16
    | exact resolve eq16 eq131775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131775
  have eq177272 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq177004
       have i₂ := eq130562
       grind)
    | exact superpose eq130562 eq177004
    | exact resolve eq177004 eq130562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130562 eq177004
  have eq177276 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq177272
  have eq177277 : (σ y) = (σ (M.op x x)) := by grind
  clear eq177276
  have eq178471 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq487 x
       have i₂ := eq177277
       grind)
    | exact superpose eq177277 eq487
    | exact resolve eq487 eq177277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq178535 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq177277
       grind)
    | exact superpose eq177277 eq10
    | exact resolve eq10 eq177277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177277
  have eq178966 : y = (M.op x x) := by
    first
    | (have i₁ := eq178535
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq178535
    | exact resolve eq178535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178535
  have eq179021 : x = (M.op x y) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq178966
       grind)
    | exact superpose eq178966 eq26
    | exact resolve eq26 eq178966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq178966
  have eq215538 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq178471
       grind)
    | exact superpose eq178471 eq16
    | exact resolve eq16 eq178471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178471
  have eq215818 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq215538
       have i₂ := eq179021
       grind)
    | exact superpose eq179021 eq215538
    | exact resolve eq215538 eq179021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179021 eq215538
  have eq215819 : False := by grind
  exact eq215819

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq275 X0 X1
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ x) (σ y)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq392 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq388
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq388
    | exact resolve eq388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq394 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq391 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq408 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq394 X0 (τ X1)
       grind)
    | exact superpose eq394 eq18
    | (have j1 := eq394 X0 (τ X1)
       grind)
    | exact resolve eq18 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq425 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq408 (τ X0) X1
       grind)
    | exact superpose eq408 eq17
    | (have j1 := eq408 (τ X0) X1
       grind)
    | exact resolve eq17 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq408
  have eq729 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq743 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq729 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq729
    | (have j0 := eq729 X0 X1
       grind)
    | exact resolve eq729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq746 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq743
    | (have j0 := eq743 X0 X1
       grind)
    | exact resolve eq743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq802 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 X1
       have i₂ := eq394 X0 X1
       grind)
    | exact superpose eq394 eq746
    | (have j0 := eq746 X0 X1
       have j1 := eq394 X0 X1
       grind)
    | exact resolve eq746 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq746
  have eq859 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       have j1 := eq425 X0 X1
       grind)
    | (have r₁ := eq802 X0 X1
       have r₂ := eq425 X0 X1
       grind)
    | exact resolve eq802 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq802
  have eq906 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq859 (σ X0) X1
       grind)
    | exact superpose eq859 eq28
    | (have j1 := eq859 (σ X0) X1
       grind)
    | exact resolve eq28 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq859
  have eq922 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq906 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq906
    | (have j0 := eq906 X0 X1
       grind)
    | exact resolve eq906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq948 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq922
    | (have j0 := eq922 X0 X1
       grind)
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1199 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq948
    | exact resolve eq948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1261 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1199 y x
       grind)
    | exact superpose eq1199 eq16
    | (have j1 := eq1199 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1199 y x
       grind)
    | exact resolve eq16 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1281 : x = (k x y) := by grind
  clear eq1261
  have eq1394 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq392
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq392
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq392 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1394
  have eq1397 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1396
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1396
    | exact resolve eq1396 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1398 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1397
    | exact resolve eq1397 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1400 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq392
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq392
    | exact resolve eq392 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq1398
  have eq1411 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1400
  have eq1412 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1411
    | exact resolve eq1411 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1413 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1412
  have eq1417 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq16
    | exact resolve eq16 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1443 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq1417
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq1417 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1445 : (M.op x y) = (k x y) := by grind
  clear eq1443
  have eq1447 : x = (M.op x y) := by
    first
    | (have i₁ := eq1445
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1445
    | exact resolve eq1445 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq1445
  have eq1449 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq1447
       grind)
    | exact superpose eq1447 eq1417
    | exact resolve eq1417 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq1447
  have eq1462 : False := by grind
  exact eq1462

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq206 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq208 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq206
    | (have j0 := eq206 X0 X1
       grind)
    | exact resolve eq206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq211 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       have j1 := eq202 X1 X0
       grind)
    | (have r₁ := eq208 X1 X0
       have r₂ := eq202 X0 X1
       grind)
    | (have r₁ := eq208 X1 (k X0 X1)
       have r₂ := eq202 X0 X1
       grind)
    | (have r₁ := eq208 X1 X1
       have r₂ := eq202 X1 X1
       grind)
    | exact resolve eq208 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq208
  have eq523 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq211 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211
    | exact resolve eq211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211 y x
       grind)
    | exact superpose eq211 eq16
    | (have j1 := eq211 y x
       grind)
    | exact resolve eq16 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq546 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq523
  have eq548 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq607 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq548 (τ X0) X1
       grind)
    | exact superpose eq548 eq18
    | (have j1 := eq548 (τ X0) X1
       grind)
    | exact resolve eq18 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq548
  have eq843 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq607 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq607
    | exact resolve eq607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq896 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq996 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq531
       have i₂ := eq896 x y
       grind)
    | exact superpose eq896 eq531
    | (have j1 := eq896 (σ x) (σ y)
       grind)
    | (have r₁ := eq531
       have r₂ := eq896 x y
       grind)
    | exact resolve eq531 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq996
  have eq1003 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq997
  have eq1041 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq531
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq531
    | exact resolve eq531 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq1003
  have eq1042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1041
  have eq1043 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1042
  have eq1058 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1043
  have eq1065 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1058
    | exact resolve eq1058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1088 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1065
       grind)
    | exact superpose eq1065 eq16
    | exact resolve eq16 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1088
       have i₂ := eq896 x y
       grind)
    | exact superpose eq896 eq1088
    | (have j1 := eq896 x y
       grind)
    | (have r₁ := eq1088
       have r₂ := eq896 x y
       grind)
    | exact resolve eq1088 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1101 : x = (M.op y y) := by grind
  clear eq1100
  have eq1139 : (M.op x y) = (k x y) := by grind
  clear eq1101
  have eq1146 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1088
       have i₂ := eq1139
       grind)
    | exact superpose eq1139 eq1088
    | exact resolve eq1088 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq1139
  have eq1149 : False := by grind
  exact eq1149

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1921 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq154 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq788 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq154 X1 X0
       grind)
    | exact superpose eq154 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq154 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq154 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq154 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq800 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq801 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq800 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq2293 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq801
    | exact resolve eq801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq2338 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2293 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2293
    | (have j0 := eq2293 X0 X1
       grind)
    | exact resolve eq2293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293
  have eq2374 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2338 X0 X1
       grind)
    | exact superpose eq2338 eq10
    | (have j1 := eq2338 X0 X1
       grind)
    | exact resolve eq10 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2418 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2374 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2374
    | (have j0 := eq2374 X0 X1
       grind)
    | exact resolve eq2374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2456 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq2418 (σ X0) X1
       grind)
    | exact superpose eq2418 eq37
    | (have j1 := eq2418 (σ X0) X1
       grind)
    | exact resolve eq37 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2418
  have eq4244 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2456 X1 (σ X0)
       grind)
    | exact superpose eq2456 eq28
    | (have j1 := eq2456 X1 (σ X0)
       grind)
    | exact resolve eq28 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2456
  have eq4305 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4244 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4244
    | (have j0 := eq4244 X0 X1
       grind)
    | exact resolve eq4244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4244
  have eq4339 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4305 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4305
    | (have j0 := eq4305 X0 X1
       grind)
    | exact resolve eq4305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305
  have eq4349 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4339 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4339
    | (have j0 := eq4339 X0 X1
       grind)
    | exact resolve eq4339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339
  have eq4552 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4349 X1 X0
       grind)
    | exact superpose eq4349 eq11
    | (have j1 := eq4349 X1 X0
       grind)
    | exact resolve eq11 eq4349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4349
  have eq5440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4552 x y
       grind)
    | exact superpose eq4552 eq16
    | (have j1 := eq4552 x y
       grind)
    | exact resolve eq16 eq4552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4552
  have eq5474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5440
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5440
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5440
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5440
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5475 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5440
       have i₂ := eq2338 x y
       grind)
    | exact superpose eq2338 eq5440
    | (have j1 := eq2338 x y
       grind)
    | (have r₁ := eq5440
       have r₂ := eq2338 x y
       grind)
    | (have r₁ := eq5440
       have r₂ := eq2338 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5440
       have r₂ := eq2338 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5440 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq5440
  have eq5478 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5475
  have eq5479 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5478
  have eq5480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5474
  have eq5481 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5480
  have eq5485 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5479
       grind)
    | exact superpose eq5479 eq16
    | exact resolve eq16 eq5479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479
  have eq5486 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5485
       have r₂ := eq22 x
       grind)
    | exact resolve eq5485 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5485
  have eq5490 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq711 x y
       have i₂ := eq5486
       grind)
    | exact superpose eq5486 eq711
    | (have j0 := eq711 x y
       grind)
    | exact resolve eq711 eq5486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq5486
  have eq5497 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5490
  have eq5498 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5497
  have eq5512 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5498
       grind)
    | exact superpose eq5498 eq16
    | exact resolve eq16 eq5498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5498
  have eq5535 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5512
       have i₂ := eq5481
       grind)
    | exact superpose eq5481 eq5512
    | exact resolve eq5512 eq5481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5481 eq5512
  have eq5536 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5535
  have eq5537 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5536
  have eq5538 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5537
       grind)
    | exact superpose eq5537 eq16
    | exact resolve eq16 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5537
  have eq5539 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5538
       have r₂ := eq22 x
       grind)
    | exact resolve eq5538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq5540 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq16
    | exact resolve eq16 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5541 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq10
    | exact resolve eq10 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq5596 : x = y := by
    first
    | (have i₁ := eq5541
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5541
    | exact resolve eq5541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5541
  have eq5597 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5540
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5540
    | exact resolve eq5540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5540
  have eq5598 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5597
       have i₂ := eq5596
       grind)
    | exact superpose eq5596 eq5597
    | exact resolve eq5597 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596 eq5597
  have eq5599 : False := by grind
  exact eq5599

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq36 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq42 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq42
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq103 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq103 X1 X1
       have r₂ := eq47 X1 X1
       grind)
    | exact resolve eq103 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq103
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq107 (σ X0) (σ X1)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq251
    | exact resolve eq251 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq251
  have eq261 : False := by grind
  exact eq261

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1924 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq453 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3374 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq453 X0 X1
       grind)
    | (have i₁ := eq9 (σ X1) X0
       have i₂ := eq453 X0 X1
       grind)
    | exact superpose eq453 eq9
    | (have j1 := eq453 X0 X1
       grind)
    | exact resolve eq9 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq3391 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3374 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq3374
    | (have j0 := eq3374 X0 X1
       grind)
    | exact resolve eq3374 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq3392 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391
  have eq3410 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3392 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3392
    | exact resolve eq3392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3507 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3410 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq3410
    | (have j0 := eq3410 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq3410 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3410
  have eq3535 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3507 X1 X0
       grind)
    | exact superpose eq3507 eq11
    | (have j1 := eq3507 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq3507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq3652 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3535 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3535
    | (have j0 := eq3535 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq3535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535
  have eq3678 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq3652 X0 (τ X1)
       grind)
    | exact superpose eq3652 eq19
    | (have j1 := eq3652 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3698 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3652 (σ X0) (σ X1)
       grind)
    | exact superpose eq3652 eq15
    | (have j1 := eq3652 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq3980 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3678 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3678
    | exact resolve eq3678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678
  have eq4046 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3980 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3980
    | (have j0 := eq3980 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3980 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3980
  have eq4391 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3698 x y
       grind)
    | exact superpose eq3698 eq16
    | (have j1 := eq3698 x y
       grind)
    | exact resolve eq16 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698
  have eq4429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4391
       have i₂ := eq4046 y x
       grind)
    | exact superpose eq4046 eq4391
    | (have j1 := eq4046 (σ x) (σ y)
       grind)
    | (have r₁ := eq4391
       have r₂ := eq4046 y x
       grind)
    | (have r₁ := eq4391
       have r₂ := eq4046 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4391
       have r₂ := eq4046 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4391 eq4046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4046 eq4391
  have eq4432 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq4429
  have eq4435 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4432
       grind)
    | exact superpose eq4432 eq16
    | exact resolve eq16 eq4432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4432
  have eq4436 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4435
       have r₂ := eq22 x
       grind)
    | exact resolve eq4435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq4437 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq16
    | exact resolve eq16 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4438 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4436
       grind)
    | exact superpose eq4436 eq10
    | exact resolve eq10 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436
  have eq4492 : x = y := by
    first
    | (have i₁ := eq4438
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4438
    | exact resolve eq4438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq4493 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4437
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq4437
    | exact resolve eq4437 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4437
  have eq4494 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4493
       have i₂ := eq4492
       grind)
    | exact superpose eq4492 eq4493
    | exact resolve eq4493 eq4492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492 eq4493
  have eq4495 : False := by grind
  exact eq4495

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1924 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq459 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3247 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq459 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq459 X0 X1
       grind)
    | exact superpose eq459 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq459 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq459 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq459 X0 X1
       grind)
    | exact resolve eq13 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3250 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3247 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3251 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq4392 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3251 X0 X1
       grind)
    | exact superpose eq3251 eq28
    | (have j1 := eq3251 X0 X1
       grind)
    | exact resolve eq28 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3251
  have eq4427 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4442 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4427 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4427
    | exact resolve eq4427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq4559 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4442 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4442
    | (have j0 := eq4442 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq4442 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4442
  have eq4591 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4559 X1 X0
       grind)
    | exact superpose eq4559 eq11
    | (have j1 := eq4559 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4711 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4591 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4591
    | (have j0 := eq4591 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq4591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591
  have eq4741 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4711 X0 (τ X1)
       grind)
    | exact superpose eq4711 eq19
    | (have j1 := eq4711 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq4711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4711 (σ X0) (σ X1)
       grind)
    | exact superpose eq4711 eq15
    | (have j1 := eq4711 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4711
  have eq4996 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4741 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4741
    | exact resolve eq4741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq5069 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4996 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4996
    | (have j0 := eq4996 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq4996 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4996
  have eq5447 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4763 x y
       grind)
    | exact superpose eq4763 eq16
    | (have j1 := eq4763 x y
       grind)
    | exact resolve eq16 eq4763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4763
  have eq5496 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5447
       have i₂ := eq5069 y x
       grind)
    | exact superpose eq5069 eq5447
    | (have j1 := eq5069 (σ x) (σ y)
       grind)
    | (have r₁ := eq5447
       have r₂ := eq5069 y x
       grind)
    | (have r₁ := eq5447
       have r₂ := eq5069 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5447
       have r₂ := eq5069 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5447 eq5069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069 eq5447
  have eq5499 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5496
  have eq5502 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5499
       grind)
    | exact superpose eq5499 eq16
    | exact resolve eq16 eq5499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5499
  have eq5503 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5502
       have r₂ := eq22 x
       grind)
    | exact resolve eq5502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5502
  have eq5504 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5503
       grind)
    | exact superpose eq5503 eq16
    | exact resolve eq16 eq5503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5505 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5503
       grind)
    | exact superpose eq5503 eq10
    | exact resolve eq10 eq5503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503
  have eq5562 : x = y := by
    first
    | (have i₁ := eq5505
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5505
    | exact resolve eq5505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505
  have eq5563 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5504
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5504
    | exact resolve eq5504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5504
  have eq5564 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5563
       have i₂ := eq5562
       grind)
    | exact superpose eq5562 eq5563
    | exact resolve eq5563 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562 eq5563
  have eq5565 : False := by grind
  exact eq5565

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pxy_Equation1924 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq465 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
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
  have eq474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq635 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq474 x y
       grind)
    | exact superpose eq474 eq16
    | (have j1 := eq474 x y
       grind)
    | exact resolve eq16 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq3075 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq465
    | exact resolve eq465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq3119 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3075 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3075
    | (have j0 := eq3075 X0 X1
       grind)
    | exact resolve eq3075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3742 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq635
       have i₂ := eq3119 x y
       grind)
    | exact superpose eq3119 eq635
    | (have j1 := eq3119 x y
       grind)
    | (have r₁ := eq635
       have r₂ := eq3119 x y
       grind)
    | (have r₁ := eq635
       have r₂ := eq3119 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq635
       have r₂ := eq3119 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq635 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq3119
  have eq3743 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
  clear eq3742
  have eq13931 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3743
       grind)
    | exact superpose eq3743 eq16
    | exact resolve eq16 eq3743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743
  have eq13932 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq13931
       have r₂ := eq22 x
       grind)
    | exact resolve eq13931 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13931
  have eq13939 : (σ x) = (M.op (M.op (σ y) (σ (M.op y y))) (σ (M.op y y))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq13932
       grind)
    | exact superpose eq13932 eq9
    | exact resolve eq9 eq13932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq13952 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13939
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq13939
    | exact resolve eq13939 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq13939
  have eq13953 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq13952
  have eq13974 : y = (M.op (M.op y (M.op y x)) (M.op y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq13953
       grind)
    | exact superpose eq13953 eq9
    | exact resolve eq9 eq13953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13953
  have eq13980 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13974
       have i₂ := eq9 x y
       grind)
    | exact superpose eq9 eq13974
    | exact resolve eq13974 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13974
  have eq13981 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13980
       grind)
    | exact superpose eq13980 eq16
    | exact resolve eq16 eq13980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13980
  have eq13982 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq13981
       have r₂ := eq22 x
       grind)
    | exact resolve eq13981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13981
  have eq13983 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13982
       grind)
    | exact superpose eq13982 eq16
    | exact resolve eq16 eq13982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13984 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13982
       grind)
    | exact superpose eq13982 eq10
    | exact resolve eq10 eq13982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13982
  have eq14145 : x = y := by
    first
    | (have i₁ := eq13984
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13984
    | exact resolve eq13984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13984
  have eq14146 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13983
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq13983
    | exact resolve eq13983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13983
  have eq14147 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14146
       have i₂ := eq14145
       grind)
    | exact superpose eq14145 eq14146
    | exact resolve eq14146 eq14145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14145 eq14146
  have eq14148 : False := by grind
  exact eq14148
