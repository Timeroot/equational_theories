import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4460`: `x ◇ (y ◇ x) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4460 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4460 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y y) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e31 X0 x
           have i₂ := b0e32 X0 x
           grind)
        | exact superpose b0e32 b0e31
        | exact resolve b0e31 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e39 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e34 (σ y)
           grind)
        | exact superpose b0e34 b0e18
        | exact resolve b0e18 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (M.op X0 X3) = (k X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X0
           have i₂ := b0e14 X3 X0
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e13 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e13
        | (have j0 := b0e13 X1 X0
           have j1 := b0e14 X2 X0
           grind)
        | (have r₁ := b0e13 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e13 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e53 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e60 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y X1) ∨ (M.op X0 X3) = (k X3 X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e52 X0 X1 x X3
           have i₂ := b0e32 X1 x
           grind)
        | exact superpose b0e32 b0e52
        | (have j0 := b0e52 X0 X1 x X3
           grind)
        | exact resolve b0e52 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e73 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op y X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 X0 x X2
           have i₂ := b0e32 X0 x
           grind)
        | exact superpose b0e32 b0e10
        | exact resolve b0e10 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e113 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e409 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e59 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e59 b0e15
        | (have j1 := b0e59 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e415 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e59 X0 X2 (τ X1)
           grind)
        | exact superpose b0e59 b0e23
        | (have j1 := b0e59 X0 X2 X2
           grind)
        | exact resolve b0e23 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e470 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e60 (σ x) (σ y) X0
           grind)
        | exact superpose b0e60 b0e16
        | (have j1 := b0e60 (σ x) x X0
           grind)
        | exact resolve b0e16 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e495 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e470 X0
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e470
        | (have j0 := b0e470 X0
           grind)
        | exact resolve b0e470 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e470
      have b0e1061 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e56 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e3032 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e415 X1 (σ X0) X2
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e415
        | (have j0 := b0e415 X1 X1 X2
           grind)
        | exact resolve b0e415 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e415
      have b0e3117 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e3032 X0 X1 X2
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e3032
        | (have j0 := b0e3032 X0 X1 X2
           grind)
        | exact resolve b0e3032 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3032
      have b0e3489 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e1061 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e1061
        | (have j0 := b0e1061 (τ X0)
           grind)
        | exact resolve b0e1061 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e1061
      have b0e3504 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e3489 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3489
        | (have j0 := b0e3489 X0
           grind)
        | exact resolve b0e3489 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3489
      have b0e3514 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e3504 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3504
        | (have j0 := b0e3504 X0
           grind)
        | exact resolve b0e3504 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3504
      have b0e4105 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e113 X0 (σ X1)
           have i₂ := b0e409 X1 X2 (σ X0)
           grind)
        | exact superpose b0e409 b0e113
        | (have j1 := b0e409 X1 X2 X2
           grind)
        | exact resolve b0e113 b0e409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113 b0e409
      have b0e4111 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e4105 X0 X1 X2
           have i₂ := b0e11 X1
           grind)
        | exact superpose b0e11 b0e4105
        | (have j0 := b0e4105 X0 X1 X2
           grind)
        | exact resolve b0e4105 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4105
      have b0e4135 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e4111 X0 X1 X2
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e4111
        | (have j0 := b0e4111 X0 X1 X2
           grind)
        | exact resolve b0e4111 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4111
      have b0e32988 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e4135 X0 x y
           grind)
        | exact superpose b0e4135 b0e16
        | (have j1 := b0e4135 X0 x x
           grind)
        | exact resolve b0e16 b0e4135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4135
      have b0e33123 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e32988 X0
           have j1 := b0e3117 X0 x X0
           grind)
        | (have r₁ := b0e32988 X0
           have r₂ := b0e3117 y x x
           grind)
        | exact resolve b0e32988 b0e3117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3117 b0e32988
      have b0e33194 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e3514 x
           have i₂ := b0e33123 x
           grind)
        | exact superpose b0e33123 b0e3514
        | (have j0 := b0e3514 x
           grind)
        | (have r₁ := b0e3514 x
           have r₂ := b0e33123 x
           grind)
        | exact resolve b0e3514 b0e33123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3514
      have b0e33237 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e23 X0 x
           have i₂ := b0e33123 (τ X0)
           grind)
        | exact superpose b0e33123 b0e23
        | exact resolve b0e23 b0e33123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e33123
      have b0e33244 : x = (M.op x x) := by grind
      clear b0e33194
      have b0e33250 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e33237 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e33237
        | exact resolve b0e33237 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33237
      have b0e33649 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e73 X0 x
           have i₂ := b0e33244
           grind)
        | exact superpose b0e33244 b0e73
        | exact resolve b0e73 b0e33244
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73 b0e33244
      have b0e36553 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e495 X0
           have i₂ := b0e33649 y
           grind)
        | exact superpose b0e33649 b0e495
        | (have j0 := b0e495 X0
           grind)
        | exact resolve b0e495 b0e33649
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e495
      have b0e36690 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e36553 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e36553
        | (have j0 := b0e36553 X0
           grind)
        | exact resolve b0e36553 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36553
      have b0e36691 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have j0 := b0e36690 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36690
      have b0e36698 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e36691 X0
           have i₂ := b0e33250 X0
           grind)
        | exact superpose b0e33250 b0e36691
        | exact resolve b0e36691 b0e33250
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33250 b0e36691
      have b0e37028 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e36698 (σ y)
           grind)
        | exact superpose b0e36698 b0e16
        | exact resolve b0e16 b0e36698
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36698
      have b0e37197 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e37028
           have i₂ := b0e33649 y
           grind)
        | exact superpose b0e33649 b0e37028
        | exact resolve b0e37028 b0e33649
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33649 b0e37028
      have b0e37228 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e37197
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e37197
        | exact resolve b0e37197 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37197
      have b0e37229 : False := by grind
      exact b0e37229
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 X0 y
           grind)
        | (have r₁ := b1e13 X0 y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e21 X0 y
           have i₂ := b1e20 (τ X0)
           grind)
        | exact superpose b1e20 b1e21
        | exact resolve b1e21 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e21
      have b1e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e48 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e28 X0
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e28
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e28 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e52 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e48 X0
           grind)
        | (have r₁ := b1e48 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e48 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e48 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48
      have b1e57 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e52 (σ y)
           grind)
        | exact superpose b1e52 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e52 (σ y)
           grind)
        | exact resolve b1e18 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52
      have b1e63 : False := by grind
      exact b1e63
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y y) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 X0 (σ y)
           grind)
        | (have r₁ := b2e13 X0 (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b2e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e24 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e20 (σ X0)
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e27 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e11 (k X0 y)
           have i₂ := b2e24 X0
           grind)
        | exact superpose b2e24 b2e11
        | exact resolve b2e11 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e28 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e27 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e27
        | exact resolve b2e27 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e47 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e28 X0
           have i₂ := b2e14 X0 y
           grind)
        | exact superpose b2e14 b2e28
        | (have j1 := b2e14 X0 y
           grind)
        | exact resolve b2e28 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e51 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e47 X0
           grind)
        | (have r₁ := b2e47 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e47 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e47 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47
      have b2e55 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e51 y
           grind)
        | exact superpose b2e51 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e51 y
           grind)
        | exact resolve b2e17 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e61 : False := by grind
      exact b2e61
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X1 x
           have i₂ := b3e10 X0 X2 x
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e19 X0 X1
           grind)
        | exact superpose b3e19 b3e11
        | exact resolve b3e11 b3e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 X0
           have i₂ := b3e14 X2 X0
           grind)
        | exact superpose b3e14 b3e13
        | (have j0 := b3e13 X1 X0
           have j1 := b3e14 X2 X0
           grind)
        | (have r₁ := b3e13 X0 X1
           have r₂ := b3e14 X0 X1
           grind)
        | exact resolve b3e13 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e33 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 X0 (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 X0 (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e35 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 X0 X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b3e33 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e31 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31
      have b3e39 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e36 (σ X0)
           grind)
        | exact superpose b3e36 b3e15
        | exact resolve b3e15 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e28 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e28
        | exact resolve b3e28 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e28
      have b3e92 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e39 y
           grind)
        | exact superpose b3e39 b3e18
        | exact resolve b3e18 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e98 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (k X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 (σ X0) (σ y) X1
           have i₂ := b3e39 X0
           grind)
        | exact superpose b3e39 b3e10
        | exact resolve b3e10 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e162 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X2 X1) = (M.op X1 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e19 X0 X1
           have i₂ := b3e37 X1 (τ X0) X2
           grind)
        | exact superpose b3e37 b3e19
        | (have j1 := b3e37 X1 X1 X2
           grind)
        | exact resolve b3e19 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e163 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e92
           have i₂ := b3e37 y y X0
           grind)
        | exact superpose b3e37 b3e92
        | (have j1 := b3e37 y x X0
           grind)
        | exact resolve b3e92 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e92
      have b3e166 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e37 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e37 b3e15
        | (have j1 := b3e37 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37
      have b3e170 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e163 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e163
      have b3e171 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (k X2 X1) = (M.op X1 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e162 X0 X1 X2
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e162
        | (have j0 := b3e162 X0 X1 X2
           grind)
        | exact resolve b3e162 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e162
      have b3e226 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e170 (τ X0)
           grind)
        | exact superpose b3e170 b3e19
        | exact resolve b3e19 b3e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e228 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e226 X0
           have i₂ := b3e36 X0
           grind)
        | exact superpose b3e36 b3e226
        | exact resolve b3e226 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36 b3e226
      have b3e639 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e34 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34
      have b3e715 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e228 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e228
        | exact resolve b3e228 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e228
      have b3e890 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 (τ X0)) = (M.op (τ X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e171 X1 (τ X0) X2
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e171
        | (have j0 := b3e171 X0 (τ X0) X2
           grind)
        | exact resolve b3e171 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e917 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X2 (σ (τ X0))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e20 X0 X1
           have i₂ := b3e171 X2 (τ X0) X1
           grind)
        | exact superpose b3e171 b3e20
        | (have j1 := b3e171 X2 (τ X0) X2
           grind)
        | exact resolve b3e20 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e171
      have b3e923 : ∀ X0 X1 X2 : G, (k X2 X0) = X2 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e917 X0 X1 X2
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e917
        | (have j0 := b3e917 X0 X1 X2
           grind)
        | exact resolve b3e917 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e917
      have b3e1330 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e35 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e35
        | (have j0 := b3e35 X1 X1
           grind)
        | exact resolve b3e35 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e1425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1330 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e1330
        | (have j0 := b3e1330 X0 X1
           grind)
        | exact resolve b3e1330 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1330
      have b3e4602 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op y (k y y))) := by
        intro X0
        first
        | (have i₁ := b3e715 (k y y)
           have i₂ := b3e98 y X0
           grind)
        | exact superpose b3e98 b3e715
        | exact resolve b3e715 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e98 b3e715
      have b3e4647 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op y (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b3e4602 X0
           have i₂ := b3e170 y
           grind)
        | exact superpose b3e170 b3e4602
        | exact resolve b3e4602 b3e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e170 b3e4602
      have b3e4796 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e639 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e639
        | (have j0 := b3e639 (τ X0)
           grind)
        | exact resolve b3e639 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e4801 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e4796 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e4796
        | (have j0 := b3e4796 X0
           grind)
        | exact resolve b3e4796 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4796
      have b3e4807 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e4801 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e4801
        | (have j0 := b3e4801 X0
           grind)
        | exact resolve b3e4801 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4801
      have b3e5438 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (σ (M.op y (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e4647 X1
           have i₂ := b3e24 y y X0
           grind)
        | (have i₁ := b3e4647 X1
           have i₂ := b3e24 y X0 y
           grind)
        | exact superpose b3e24 b3e4647
        | exact resolve b3e4647 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24 b3e4647
      have b3e6110 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e5438 x X1
           have i₂ := b3e10 y x X0
           grind)
        | exact superpose b3e10 b3e5438
        | exact resolve b3e5438 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5438
      have b3e6456 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e166 x y X0
           grind)
        | exact superpose b3e166 b3e16
        | (have j1 := b3e166 x x X0
           grind)
        | exact resolve b3e16 b3e166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e166
      have b3e23781 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X0) y)) = (σ (M.op (M.op X2 X2) y)) := by
        intro X0 X2
        first
        | (have i₁ := b3e6110 X2 x
           have i₂ := b3e6110 X0 x
           grind)
        | exact superpose b3e6110 b3e6110
        | exact resolve b3e6110 b3e6110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e38220 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e4807 X0
           have i₂ := b3e890 X0 X0 X1
           grind)
        | exact superpose b3e890 b3e4807
        | (have j0 := b3e4807 X0
           have j1 := b3e890 X0 X1 X1
           grind)
        | (have r₁ := b3e4807 X0
           have r₂ := b3e890 X0 X0 x
           grind)
        | exact resolve b3e4807 b3e890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e890
      have b3e38280 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b3e38220 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38220
      have b3e53348 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e639 (τ X0)
           have i₂ := b3e38280 X0 (τ X0)
           grind)
        | exact superpose b3e38280 b3e639
        | (have j0 := b3e639 (τ X0)
           have j1 := b3e38280 (σ (τ X0)) x
           grind)
        | exact resolve b3e639 b3e38280
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38280
      have b3e53377 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e53348 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e53348
        | (have j0 := b3e53348 X0
           grind)
        | exact resolve b3e53348 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e53348
      have b3e53465 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e53377 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e53377
        | (have j0 := b3e53377 X0
           grind)
        | exact resolve b3e53377 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e53377
      have b3e53466 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b3e53465 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e53465
      have b3e146695 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e53466 X0
           have i₂ := b3e923 X0 (τ X0) X1
           grind)
        | exact superpose b3e923 b3e53466
        | (have j0 := b3e53466 X0
           have j1 := b3e923 X0 X1 X1
           grind)
        | exact resolve b3e53466 b3e923
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e923 b3e53466
      have b3e146721 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e146695 X0 X1
           have j1 := b3e13 X1 X0
           grind)
        | (have r₁ := b3e146695 X1 X1
           have r₂ := b3e13 X0 X1
           grind)
        | exact resolve b3e146695 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e146695
      have b3e146770 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e146721 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e146721
        | (have j0 := b3e146721 X0 X1
           grind)
        | exact resolve b3e146721 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e146721
      have b3e147967 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e146770 (τ X0) X1
           have i₂ := b3e50 X0 X0
           grind)
        | exact superpose b3e50 b3e146770
        | (have j0 := b3e146770 (τ X0) X1
           grind)
        | exact resolve b3e146770 b3e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e50 b3e146770
      have b3e150149 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e6456 X0
           have i₂ := b3e1425 y x
           grind)
        | exact superpose b3e1425 b3e6456
        | (have j0 := b3e6456 X0
           have j1 := b3e1425 X0 x
           grind)
        | (have r₁ := b3e6456 X0
           have r₂ := b3e1425 y x
           grind)
        | exact resolve b3e6456 b3e1425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1425 b3e6456
      have b3e150151 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e150149 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e150149
      have b3e150190 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e147967 (σ x) X0
           have i₂ := b3e150151 (σ x)
           grind)
        | exact superpose b3e150151 b3e147967
        | (have j0 := b3e147967 (σ x) X0
           grind)
        | exact resolve b3e147967 b3e150151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e147967 b3e150151
      have b3e150224 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e150190 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e150190
      have b3e150244 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e150224 X0
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e150224
        | exact resolve b3e150224 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e150224
      have b3e150254 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e150244 X0
           have j1 := b3e13 X0 x
           grind)
        | (have r₁ := b3e150244 X0
           have r₂ := b3e13 X0 x
           grind)
        | exact resolve b3e150244 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e150244
      have b3e150440 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e639 x
           have i₂ := b3e150254 x
           grind)
        | exact superpose b3e150254 b3e639
        | (have j0 := b3e639 x
           grind)
        | exact resolve b3e639 b3e150254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e639
      have b3e150442 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e4807 x
           have i₂ := b3e150254 x
           grind)
        | exact superpose b3e150254 b3e4807
        | (have j0 := b3e4807 x
           grind)
        | (have r₁ := b3e4807 x
           have r₂ := b3e150254 x
           grind)
        | exact resolve b3e4807 b3e150254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4807 b3e150254
      have b3e150509 : x = (M.op x x) := by grind
      clear b3e150442
      have b3e150510 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e150440
      have b3e150825 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0
        first
        | (have i₁ := b3e23781 x X0
           have i₂ := b3e150509
           grind)
        | exact superpose b3e150509 b3e23781
        | exact resolve b3e23781 b3e150509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23781 b3e150509
      have b3e154356 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0
        first
        | (have i₁ := b3e6110 X0 (σ x)
           have i₂ := b3e150510
           grind)
        | exact superpose b3e150510 b3e6110
        | exact resolve b3e6110 b3e150510
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e6110 b3e150510
      have b3e154508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e154356 x
           have i₂ := b3e150825 x
           grind)
        | exact superpose b3e150825 b3e154356
        | exact resolve b3e154356 b3e150825
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e150825 b3e154356
      have b3e154590 : False := by grind
      exact b3e154590

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4461 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4461 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X1 X2) X2 X3
           have i₂ := b0e10 X2 X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
        intro X1
        first
        | (have i₁ := b0e37 x X1
           have i₂ := b0e38 x X1
           grind)
        | exact superpose b0e38 b0e37
        | exact resolve b0e37 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e60 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e14 X3 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X2 X2)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op y X2) ∨ (k X3 X0) = (M.op X3 X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e60 X0 x X2 X3
           have i₂ := b0e38 x X2
           grind)
        | exact superpose b0e38 b0e60
        | (have j0 := b0e60 X0 x X2 X3
           grind)
        | exact resolve b0e60 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e74 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e38 (M.op X0 X1) X1
           have i₂ := b0e38 X1 X0
           grind)
        | exact superpose b0e38 b0e38
        | exact resolve b0e38 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op y (M.op X2 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e38 X1 (M.op X2 X2)
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e38
        | exact resolve b0e38 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e78 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e38 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e38
        | exact resolve b0e38 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 : G, (M.op y (σ y)) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 X0 (σ y)
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e38
        | exact resolve b0e38 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X2 X2) X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 x X0 X2
           have i₂ := b0e38 x X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e85 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (M.op X0 X1) X1 X2
           have i₂ := b0e38 X1 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90 : (M.op y y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e79 x
           have i₂ := b0e38 x y
           grind)
        | exact superpose b0e38 b0e79
        | exact resolve b0e79 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e91 : ∀ X1 X2 : G, (M.op X1 (M.op y X1)) = (M.op y (M.op X2 X2)) := by
        intro X1 X2
        first
        | (have i₁ := b0e77 x X1 X2
           have i₂ := b0e38 x X1
           grind)
        | exact superpose b0e38 b0e77
        | exact resolve b0e77 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e93 : ∀ X2 : G, (M.op y y) = (M.op y (M.op X2 X2)) := by
        intro X2
        first
        | (have i₁ := b0e91 x X2
           have i₂ := b0e38 x y
           grind)
        | exact superpose b0e38 b0e91
        | exact resolve b0e91 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91
      have b0e100 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e624 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e61 (σ X1) (σ X0)
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e61
        | exact resolve b0e61 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e631 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e61 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e909 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) X1)) = (M.op y (M.op X3 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e38 (M.op (M.op X2 X2) X3) (M.op X3 X1)
           have i₂ := b0e31 X2 X3 X1 X0
           grind)
        | exact superpose b0e31 b0e38
        | exact resolve b0e38 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e912 : ∀ X1 X2 X3 : G, (M.op y (M.op X3 X1)) = (M.op (M.op (M.op X2 X2) X3) (M.op y X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e909 x X1 X2 X3
           have i₂ := b0e84 X1 x
           grind)
        | exact superpose b0e84 b0e909
        | exact resolve b0e909 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e909
      have b0e1030 : ∀ X1 X3 : G, (M.op y (M.op X3 X1)) = (M.op (M.op y X3) (M.op y X1)) := by
        intro X1 X3
        first
        | (have i₁ := b0e912 X1 x X3
           have i₂ := b0e84 X3 x
           grind)
        | exact superpose b0e84 b0e912
        | exact resolve b0e912 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e912
      have b0e2176 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) y) ∨ (k X3 X1) = (M.op X3 X1) ∨ (M.op y X2) = (k y X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e71 X1 X2 X3
           have i₂ := b0e62 X2 y X0
           grind)
        | exact superpose b0e62 b0e71
        | (have j0 := b0e71 X1 X2 X3
           have j1 := b0e62 X1 X3 X2
           grind)
        | exact resolve b0e71 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e2212 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e38 X0 (M.op X2 X2)
           have i₂ := b0e62 X1 X0 X2
           grind)
        | (have i₁ := b0e38 X0 X1
           have i₂ := b0e62 X0 X1 X2
           grind)
        | exact superpose b0e62 b0e38
        | (have j1 := b0e62 X1 X0 X2
           grind)
        | exact resolve b0e38 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e2248 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e2212 X0 X1 x
           have i₂ := b0e93 x
           grind)
        | exact superpose b0e93 b0e2212
        | (have j0 := b0e2212 X0 X1 x
           grind)
        | exact resolve b0e2212 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2212
      have b0e2279 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op y y) ∨ (k X3 X1) = (M.op X3 X1) ∨ (M.op y X2) = (k y X2) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e2176 x X1 X2 X3
           have i₂ := b0e84 y x
           grind)
        | exact superpose b0e84 b0e2176
        | (have j0 := b0e2176 x X1 X2 X3
           grind)
        | exact resolve b0e2176 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2176
      have b0e2517 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e78
           grind)
        | exact superpose b0e78 b0e16
        | exact resolve b0e16 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e2685 : ∀ X0 : G, (σ X0) = (M.op y (σ y)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e42 (σ y)
           have i₂ := b0e66 y X0
           grind)
        | exact superpose b0e66 b0e42
        | (have j1 := b0e66 y X0
           grind)
        | exact resolve b0e42 b0e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e66 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e2728 : ∀ X0 : G, (σ X0) = (M.op y y) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e2685 X0
           have i₂ := b0e90
           grind)
        | exact superpose b0e90 b0e2685
        | (have j0 := b0e2685 X0
           grind)
        | exact resolve b0e2685 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2685
      have b0e2763 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e2728 X0
           have i₂ := b0e42 (σ X0)
           grind)
        | exact superpose b0e42 b0e2728
        | (have j0 := b0e2728 X0
           grind)
        | exact resolve b0e2728 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2728
      have b0e2943 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e100
      have b0e2962 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2943 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e2943
        | exact resolve b0e2943 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2943
      have b0e3002 : y ≠ (M.op x y) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e631 y x
           have i₂ := b0e80
           grind)
        | exact superpose b0e80 b0e631
        | (have j0 := b0e631 y x
           grind)
        | exact resolve b0e631 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e631
      have b0e4561 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op y (M.op X0 X0))) := by
        intro X0
        grind
      clear b0e1030
      have b0e4619 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e4561 X0
           have i₂ := b0e93 X0
           grind)
        | exact superpose b0e93 b0e4561
        | exact resolve b0e4561 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4561
      have b0e6764 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b0e2711 (M.op y y)
           have i₂ := b0e4619 y
           grind)
        | exact superpose b0e4619 b0e2711
        | (have j0 := b0e2711 (M.op y y)
           grind)
        | exact resolve b0e2711 b0e4619
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4619
      have b0e6776 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b0e6764
      have b0e10313 : (M.op y y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e2248 y x
           have i₂ := b0e80
           grind)
        | exact superpose b0e80 b0e2248
        | exact resolve b0e2248 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2248
      have b0e10482 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e10313
           have i₂ := b0e38 y x
           grind)
        | exact superpose b0e38 b0e10313
        | exact resolve b0e10313 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10313
      have b0e10555 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e10482
           have i₂ := b0e80
           grind)
        | exact superpose b0e80 b0e10482
        | exact resolve b0e10482 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10482
      have b0e11605 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e42 (σ X0)
           have i₂ := b0e624 y X0
           grind)
        | exact superpose b0e624 b0e42
        | (have j1 := b0e624 y X0
           grind)
        | exact resolve b0e42 b0e624
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e624
      have b0e28996 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e2763 x
           have i₂ := b0e10555
           grind)
        | exact superpose b0e10555 b0e2763
        | (have j0 := b0e2763 x
           grind)
        | exact resolve b0e2763 b0e10555
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10555
      have b0e29008 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op y y) := by
        first
        | (have r₁ := b0e28996
           have r₂ := b0e2517
           grind)
        | exact resolve b0e28996 b0e2517
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28996
      have b0e41235 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y y) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e2279 X0 X0 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2279
      have b0e41236 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e41235 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41235
      have b0e43833 : ∀ X0 : G, y = (k y (M.op X0 X0)) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        grind
      clear b0e41236
      have b0e47774 : (M.op y y) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b0e93 (σ (M.op y y))
           have i₂ := b0e6776
           grind)
        | exact superpose b0e6776 b0e93
        | exact resolve b0e93 b0e6776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e47802 : (M.op y (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b0e38 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b0e6776
           grind)
        | exact superpose b0e6776 b0e38
        | exact resolve b0e38 b0e6776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e47855 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
        first
        | (have i₁ := b0e47802
           have i₂ := b0e6776
           grind)
        | exact superpose b0e6776 b0e47802
        | exact resolve b0e47802 b0e6776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6776 b0e47802
      have b0e47895 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e47855
           have i₂ := b0e47774
           grind)
        | exact superpose b0e47774 b0e47855
        | exact resolve b0e47855 b0e47774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47774 b0e47855
      have b0e82142 : y = (k y y) ∨ (M.op y x) = (k y x) := by
        first
        | (have i₁ := b0e43833 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e43833
        | (have j0 := b0e43833 x
           grind)
        | exact resolve b0e43833 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43833
      have b0e82172 : y = (k y y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e82142
           have i₂ := b0e80
           grind)
        | exact superpose b0e80 b0e82142
        | exact resolve b0e82142 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80 b0e82142
      have b0e82961 : y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e82172
           grind)
        | exact superpose b0e82172 b0e14
        | (have j0 := b0e14 y y
           grind)
        | exact resolve b0e14 b0e82172
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82172
      have b0e82969 : (M.op x y) = (k y x) ∨ y = (M.op y y) := by grind
      clear b0e82961
      have b0e83101 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e2763 x
           have i₂ := b0e82969
           grind)
        | exact superpose b0e82969 b0e2763
        | (have j0 := b0e2763 x
           grind)
        | exact resolve b0e2763 b0e82969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82969
      have b0e83123 : (σ x) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b0e83101
           have r₂ := b0e2517
           grind)
        | exact resolve b0e83101 b0e2517
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83101
      have b0e83321 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e74 y y
           have i₂ := b0e83123
           grind)
        | exact superpose b0e83123 b0e74
        | exact resolve b0e74 b0e83123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e83322 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 X0) y) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e85 y y x
           have i₂ := b0e83123
           grind)
        | exact superpose b0e83123 b0e85
        | exact resolve b0e85 b0e83123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85 b0e83123
      have b0e83344 : (M.op (σ x) (σ x)) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e83322 x
           have i₂ := b0e84 y x
           grind)
        | exact superpose b0e84 b0e83322
        | exact resolve b0e83322 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84 b0e83322
      have b0e83345 : y = (M.op y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e83321
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e83321
        | exact resolve b0e83321 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83321
      have b0e83390 : (σ y) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e83344
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e83344
        | exact resolve b0e83344 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83344
      have b0e84824 : (σ x) = (σ y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e47895
           have i₂ := b0e83345
           grind)
        | exact superpose b0e83345 b0e47895
        | exact resolve b0e47895 b0e83345
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83345
      have b0e85243 : y = (k y (τ (M.op (σ x) (σ x)))) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e2962 y
           have i₂ := b0e84824
           grind)
        | exact superpose b0e84824 b0e2962
        | exact resolve b0e2962 b0e84824
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2962 b0e84824
      have b0e85252 : y = (k y (τ (σ y))) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e85243
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e85243
        | exact resolve b0e85243 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85243
      have b0e85280 : y = (k y y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e85252
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e85252
        | exact resolve b0e85252 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85252
      have b0e86177 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e85280
           grind)
        | exact superpose b0e85280 b0e14
        | (have j0 := b0e14 y y
           grind)
        | exact resolve b0e14 b0e85280
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85280
      have b0e86196 : y = (M.op y y) ∨ y = (σ y) := by grind
      clear b0e86177
      have b0e86281 : y = (σ y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e47895
           have i₂ := b0e86196
           grind)
        | exact superpose b0e86196 b0e47895
        | exact resolve b0e47895 b0e86196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47895 b0e86196
      have b0e86414 : y = (σ y) := by grind
      clear b0e86281
      have b0e86560 : y = (τ y) := by
        first
        | (have i₁ := b0e11 y
           have i₂ := b0e86414
           grind)
        | exact superpose b0e86414 b0e11
        | exact resolve b0e11 b0e86414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e89428 : (σ y) ≠ (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y y)) := by
        first
        | (have i₁ := b0e2711 y
           have i₂ := b0e11605 y
           grind)
        | exact superpose b0e11605 b0e2711
        | (have j0 := b0e2711 y
           have j1 := b0e11605 y
           grind)
        | (have r₁ := b0e2711 y
           have r₂ := b0e11605 y
           grind)
        | exact resolve b0e2711 b0e11605
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11605
      have b0e89453 : (σ y) ≠ (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have j1 := b0e2711 y
           grind)
        | (have r₁ := b0e89428
           have r₂ := b0e2711 y
           grind)
        | exact resolve b0e89428 b0e2711
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2711 b0e89428
      have b0e89477 : (σ y) ≠ (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e89453
           have i₂ := b0e90
           grind)
        | exact superpose b0e90 b0e89453
        | exact resolve b0e89453 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89453
      have b0e89485 : y ≠ (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e89477
           have i₂ := b0e86414
           grind)
        | exact superpose b0e86414 b0e89477
        | exact resolve b0e89477 b0e86414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89477
      have b0e89490 : (σ y) = (M.op y (σ y)) ∨ y ≠ (M.op y y) := by
        first
        | (have i₁ := b0e89485
           have i₂ := b0e42 (σ y)
           grind)
        | exact superpose b0e42 b0e89485
        | exact resolve b0e89485 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e89485
      have b0e89491 : (σ y) = (M.op y y) ∨ y ≠ (M.op y y) := by
        first
        | (have i₁ := b0e89490
           have i₂ := b0e90
           grind)
        | exact superpose b0e90 b0e89490
        | exact resolve b0e89490 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90 b0e89490
      have b0e89492 : (σ y) = (M.op y y) := by
        first
        | (have r₁ := b0e89491
           have r₂ := b0e83390
           grind)
        | exact resolve b0e89491 b0e83390
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83390 b0e89491
      have b0e89493 : y = (M.op y y) := by
        first
        | (have i₁ := b0e89492
           have i₂ := b0e86414
           grind)
        | exact superpose b0e86414 b0e89492
        | exact resolve b0e89492 b0e86414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89492
      have b0e89516 : y = (M.op x y) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e29008
           have i₂ := b0e89493
           grind)
        | exact superpose b0e89493 b0e29008
        | exact resolve b0e29008 b0e89493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29008
      have b0e93569 : (σ y) ≠ (M.op y (σ x)) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e2517
           have i₂ := b0e89516
           grind)
        | exact superpose b0e89516 b0e2517
        | exact resolve b0e2517 b0e89516
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2517
      have b0e93570 : y ≠ y ∨ y = (k y x) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e3002
           have i₂ := b0e89516
           grind)
        | exact superpose b0e89516 b0e3002
        | (have r₁ := b0e3002
           have r₂ := b0e89516
           grind)
        | exact resolve b0e3002 b0e89516
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3002 b0e89516
      have b0e93623 : y = (k y x) ∨ y = (σ x) := by grind
      clear b0e93570
      have b0e93655 : y ≠ (M.op y (σ x)) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e93569
           have i₂ := b0e86414
           grind)
        | exact superpose b0e86414 b0e93569
        | exact resolve b0e93569 b0e86414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93569
      have b0e95001 : (σ y) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e2763 x
           have i₂ := b0e93623
           grind)
        | exact superpose b0e93623 b0e2763
        | (have j0 := b0e2763 x
           grind)
        | exact resolve b0e2763 b0e93623
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2763 b0e93623
      have b0e95039 : y = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e95001
           have i₂ := b0e86414
           grind)
        | exact superpose b0e86414 b0e95001
        | exact resolve b0e95001 b0e86414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86414 b0e95001
      have b0e95056 : (σ x) = (M.op y y) ∨ y = (σ x) := by
        first
        | (have r₁ := b0e95039
           have r₂ := b0e93655
           grind)
        | exact resolve b0e95039 b0e93655
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93655 b0e95039
      have b0e95060 : y = (σ x) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e95056
           have i₂ := b0e89493
           grind)
        | exact superpose b0e89493 b0e95056
        | exact resolve b0e95056 b0e89493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89493 b0e95056
      have b0e95061 : y = (σ x) := by grind
      clear b0e95060
      have b0e95106 : x = (τ y) := by
        first
        | (have i₁ := b0e11 x
           have i₂ := b0e95061
           grind)
        | exact superpose b0e95061 b0e11
        | exact resolve b0e11 b0e95061
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95061
      have b0e95298 : x = y := by
        first
        | (have i₁ := b0e86560
           have i₂ := b0e95106
           grind)
        | exact superpose b0e95106 b0e86560
        | exact resolve b0e86560 b0e95106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86560 b0e95106
      have b0e95541 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e95298
           grind)
        | exact superpose b0e95298 b0e16
        | exact resolve b0e16 b0e95298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95298
      have b0e95869 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e95541
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e95541
        | exact resolve b0e95541 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95541
      have b0e95940 : False := by grind
      exact b0e95940
    · have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : x = (k x y) := by grind
      have b1e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 (σ x) X0
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 (σ x) X0
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 (σ x) (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e82 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e22 X1 X0
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e449 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e59 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59
      have b1e469 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e63 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e63
      have b1e470 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e469
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e469
        | exact resolve b1e469 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e469
      have b1e471 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e470
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e470
        | exact resolve b1e470 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e470
      have b1e472 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e471
           grind)
        | exact superpose b1e471 b1e16
        | exact resolve b1e16 b1e471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e471
      have b1e594 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e82
      have b1e609 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e594 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e594
        | exact resolve b1e594 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e594
      have b1e2077 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e449 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e449
        | (have j0 := b1e449 x x
           grind)
        | exact resolve b1e449 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e449
      have b1e2390 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e64 x x
           grind)
        | exact superpose b1e64 b1e18
        | (have j1 := b1e64 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e64 x y
           grind)
        | exact resolve b1e18 b1e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e64
      have b1e5177 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e2390
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e2390
        | (have j1 := b1e14 (σ x) (σ x)
           grind)
        | exact resolve b1e2390 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2390
      have b1e5193 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e5177
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e5177
        | exact resolve b1e5177 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5177
      have b1e5194 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e5193
      have b1e5197 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e5194
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e5194
        | exact resolve b1e5194 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5194
      have b1e5203 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e609 x
           have i₂ := b1e5197
           grind)
        | exact superpose b1e5197 b1e609
        | exact resolve b1e609 b1e5197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e609 b1e5197
      have b1e5253 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e5203
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e5203
        | exact resolve b1e5203 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5203
      have b1e5258 : x = (k x x) := by
        first
        | (have r₁ := b1e5253
           have r₂ := b1e2077
           grind)
        | exact resolve b1e5253 b1e2077
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2077 b1e5253
      have b1e5276 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e5258
           grind)
        | exact superpose b1e5258 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e5258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5258
      have b1e5281 : x = (M.op x x) := by grind
      clear b1e5276
      have b1e5315 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e5281
           grind)
        | exact superpose b1e5281 b1e17
        | exact resolve b1e17 b1e5281
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5281
      have b1e5904 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e472
           have i₂ := b1e5315
           grind)
        | exact superpose b1e5315 b1e472
        | exact resolve b1e472 b1e5315
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e472
      have b1e5934 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e5904
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e5904
        | exact resolve b1e5904 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5904
      have b1e5943 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e5934
           have i₂ := b1e5315
           grind)
        | exact superpose b1e5315 b1e5934
        | exact resolve b1e5934 b1e5315
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5315 b1e5934
      have b1e5944 : False := by grind
      exact b1e5944
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x x) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e20
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e20
        | exact resolve b2e20 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e26 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e21
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : x = (k x y) := by
        first
        | (have i₁ := b2e26
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e26
        | exact resolve b2e26 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) (σ x) X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op X1 X2) X2 X3
           have i₂ := b2e10 X2 X1 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X1 (M.op X2 X2) X3
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 X1 (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e40 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op (σ y) X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b2e32 x X1 X2 X3
           have i₂ := b2e35 x X1
           grind)
        | exact superpose b2e35 b2e32
        | exact resolve b2e32 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e41 : ∀ X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (σ y) (σ y)) := by
        intro X2 X3
        first
        | (have i₁ := b2e40 x X2 X3
           have i₂ := b2e35 x (σ y)
           grind)
        | exact superpose b2e35 b2e40
        | exact resolve b2e40 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40
      have b2e54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e55 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 X1 X2
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e10 X0 X1 X2
           have i₂ := b2e14 X0 (M.op X1 X0)
           grind)
        | exact superpose b2e14 b2e10
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e10 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e60 : x = (M.op x y) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e61 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e21
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e21 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e62 : (σ (M.op x y)) = (σ x) := by
        first
        | (have r₁ := b2e61
           have r₂ := b2e17
           grind)
        | exact resolve b2e61 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61
      have b2e63 : x = (M.op x y) := by
        first
        | (have r₁ := b2e60
           have r₂ := b2e17
           grind)
        | exact resolve b2e60 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e60
      have b2e83 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 X1) (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e35 (M.op X0 X1) X1
           have i₂ := b2e35 X1 X0
           grind)
        | exact superpose b2e35 b2e35
        | exact resolve b2e35 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e88 : (M.op (σ y) x) = (M.op y x) := by
        first
        | (have i₁ := b2e35 y x
           have i₂ := b2e63
           grind)
        | exact superpose b2e63 b2e35
        | exact resolve b2e35 b2e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e63
      have b2e91 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (σ y) X0) := by
        intro X0 X2
        first
        | (have i₁ := b2e10 x X0 X2
           have i₂ := b2e35 x X0
           grind)
        | exact superpose b2e35 b2e10
        | exact resolve b2e10 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e99 : (M.op (σ y) (σ y)) = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b2e35 x (σ y)
           have i₂ := b2e88
           grind)
        | exact superpose b2e88 b2e35
        | exact resolve b2e35 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e100 : (M.op (σ y) (σ y)) = (M.op (σ y) y) := by
        first
        | (have i₁ := b2e99
           have i₂ := b2e35 x y
           grind)
        | exact superpose b2e35 b2e99
        | exact resolve b2e99 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e99
      have b2e360 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 (σ x) (M.op X0 X0) X1
           have i₂ := b2e30 X0
           grind)
        | exact superpose b2e30 b2e10
        | exact resolve b2e10 b2e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e361 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e360 x x
           have i₂ := b2e41 x x
           grind)
        | exact superpose b2e41 b2e360
        | exact resolve b2e360 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41 b2e360
      have b2e370 : (M.op (σ y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e361
           have i₂ := b2e100
           grind)
        | exact superpose b2e100 b2e361
        | exact resolve b2e361 b2e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e361
      have b2e713 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) X1)) = (M.op (σ y) (M.op X3 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e35 (M.op (M.op X2 X2) X3) (M.op X3 X1)
           have i₂ := b2e31 X2 X3 X1 X0
           grind)
        | exact superpose b2e31 b2e35
        | exact resolve b2e35 b2e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e716 : ∀ X1 X2 X3 : G, (M.op (σ y) (M.op X3 X1)) = (M.op (M.op (M.op X2 X2) X3) (M.op (σ y) X1)) := by
        intro X1 X2 X3
        first
        | (have i₁ := b2e713 x X1 X2 X3
           have i₂ := b2e91 X1 x
           grind)
        | exact superpose b2e91 b2e713
        | exact resolve b2e713 b2e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e713
      have b2e813 : ∀ X1 X3 : G, (M.op (σ y) (M.op X3 X1)) = (M.op (M.op (σ y) X3) (M.op (σ y) X1)) := by
        intro X1 X3
        first
        | (have i₁ := b2e716 X1 x X3
           have i₂ := b2e91 X3 x
           grind)
        | exact superpose b2e91 b2e716
        | exact resolve b2e716 b2e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e91 b2e716
      have b2e3254 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e58 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e58
        | exact resolve b2e58 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58
      have b2e4010 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e3254
           grind)
        | exact superpose b2e3254 b2e11
        | exact resolve b2e11 b2e3254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3254
      have b2e4026 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e4010
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e4010
        | exact resolve b2e4010 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4010
      have b2e4263 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e54 x x
           have i₂ := b2e4026
           grind)
        | exact superpose b2e4026 b2e54
        | exact resolve b2e54 b2e4026
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54 b2e4026
      have b2e4266 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e4263
           have r₂ := b2e17
           grind)
        | exact resolve b2e4263 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4263
      have b2e4437 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e4266
           grind)
        | exact superpose b2e4266 b2e11
        | exact resolve b2e11 b2e4266
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4266
      have b2e4453 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e4437
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e4437
        | exact resolve b2e4437 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4437
      have b2e4454 : x = y := by grind
      clear b2e4453
      have b2e4469 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ y) y) ∨ (M.op (σ y) y) = (k (σ x) (M.op (σ x) (σ y))) := by
        intro X0
        first
        | (have i₁ := b2e55 (M.op (σ x) (σ y)) (σ x) x
           have i₂ := b2e370
           grind)
        | exact superpose b2e370 b2e55
        | exact resolve b2e55 b2e370
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55
      have b2e4470 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) y) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b2e83 (σ x) (M.op (σ x) (σ y))
           have i₂ := b2e370
           grind)
        | exact superpose b2e370 b2e83
        | exact resolve b2e83 b2e370
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e83 b2e370
      have b2e4473 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op y (σ x))) := by
        first
        | (have i₁ := b2e4470
           have i₂ := b2e813 (σ x) y
           grind)
        | exact superpose b2e813 b2e4470
        | exact resolve b2e4470 b2e813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e813 b2e4470
      have b2e4474 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) x) ∨ (M.op (σ y) y) = (k (σ x) (M.op (σ x) (σ y))) := by
        intro X0
        first
        | (have i₁ := b2e4469 X0
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4469
        | exact resolve b2e4469 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4469
      have b2e4483 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op x (σ x))) := by
        first
        | (have i₁ := b2e4473
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4473
        | exact resolve b2e4473 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4473
      have b2e4484 : (M.op (σ x) (σ y)) = (M.op (σ x) x) ∨ (M.op (σ y) y) = (k (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e4474 x
           have i₂ := b2e30 x
           grind)
        | exact superpose b2e30 b2e4474
        | exact resolve b2e4474 b2e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30 b2e4474
      have b2e4490 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) x) := by
        first
        | (have i₁ := b2e4483
           have i₂ := b2e35 (σ x) x
           grind)
        | exact superpose b2e35 b2e4483
        | exact resolve b2e4483 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4483
      have b2e4491 : (M.op (σ x) (σ x)) = (M.op (σ x) x) ∨ (M.op (σ y) y) = (k (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e4484
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4484
        | exact resolve b2e4484 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4484
      have b2e4495 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op y x) := by
        first
        | (have i₁ := b2e4490
           have i₂ := b2e88
           grind)
        | exact superpose b2e88 b2e4490
        | exact resolve b2e4490 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e88 b2e4490
      have b2e4496 : (σ y) = (M.op (σ x) x) ∨ (M.op (σ y) y) = (k (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e4491
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e4491
        | exact resolve b2e4491 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4491
      have b2e4499 : (M.op x x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b2e4495
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4495
        | exact resolve b2e4495 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4495
      have b2e4500 : (σ x) = (M.op (σ x) x) ∨ (M.op (σ y) y) = (k (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e4496
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4496
        | exact resolve b2e4496 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4496
      have b2e4502 : (M.op x x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e4499
           have i₂ := b2e35 (σ x) (σ x)
           grind)
        | exact superpose b2e35 b2e4499
        | exact resolve b2e4499 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e35 b2e4499
      have b2e4503 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e4500
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4500
        | exact resolve b2e4500 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4500
      have b2e4505 : (M.op x x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e4502
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4502
        | exact resolve b2e4502 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4502
      have b2e4506 : (σ x) = (M.op (σ x) x) ∨ (σ x) = (M.op (σ x) x) := by grind
      clear b2e4503
      have b2e4507 : (σ x) = (M.op (σ x) x) := by grind
      clear b2e4506
      have b2e4509 : (σ y) = (M.op x x) := by
        first
        | (have i₁ := b2e4505
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e4505
        | exact resolve b2e4505 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4505
      have b2e4510 : (σ x) = (M.op x x) := by
        first
        | (have i₁ := b2e4509
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e4509
        | exact resolve b2e4509 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4509
      have b2e4511 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e16
        | exact resolve b2e16 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4514 : (σ x) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e62
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e62
        | exact resolve b2e62 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62
      have b2e4522 : (M.op (σ x) (σ x)) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e100
           have i₂ := b2e4454
           grind)
        | exact superpose b2e4454 b2e100
        | exact resolve b2e100 b2e4454
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e100 b2e4454
      have b2e4535 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e4522
           have i₂ := b2e4507
           grind)
        | exact superpose b2e4507 b2e4522
        | exact resolve b2e4522 b2e4507
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4507 b2e4522
      have b2e4539 : (σ x) = (σ (σ x)) := by
        first
        | (have i₁ := b2e4514
           have i₂ := b2e4510
           grind)
        | exact superpose b2e4510 b2e4514
        | exact resolve b2e4514 b2e4510
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4514
      have b2e4540 : (M.op (σ x) (σ x)) ≠ (σ (σ x)) := by
        first
        | (have i₁ := b2e4511
           have i₂ := b2e4510
           grind)
        | exact superpose b2e4510 b2e4511
        | exact resolve b2e4511 b2e4510
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4510 b2e4511
      have b2e4546 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e4540
           have i₂ := b2e4539
           grind)
        | exact superpose b2e4539 b2e4540
        | exact resolve b2e4540 b2e4539
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4539 b2e4540
      have b2e4549 : False := by grind
      exact b2e4549
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e43 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e178 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e43 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e43
      have b3e179 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e178
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e178
        | exact resolve b3e178 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e178
      have b3e259 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e179
           grind)
        | exact superpose b3e179 b3e16
        | exact resolve b3e16 b3e179
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e179
      have b3e347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e259
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e259
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e259 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e259
      have b3e348 : y = (M.op x x) := by grind
      clear b3e347
      have b3e350 : False := by grind
      exact b3e350

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4461 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4461 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y y) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ y) (σ y) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
        intro X1
        first
        | (have i₁ := b0e33 x X1
           have i₂ := b0e34 x X1
           grind)
        | exact superpose b0e34 b0e33
        | exact resolve b0e33 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e40 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e29
        | exact resolve b0e29 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e50 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op X0 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (σ y) X1
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e52 : ∀ X1 : G, (M.op y y) = (M.op (M.op X1 X1) (σ y)) := by
        intro X1
        first
        | (have i₁ := b0e50 x X1
           have i₂ := b0e34 x y
           grind)
        | exact superpose b0e34 b0e50
        | exact resolve b0e50 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e50
      have b0e54 : (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e52 x
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e52
        | exact resolve b0e52 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e56 : y = (σ y) := by
        first
        | (have i₁ := b0e54
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e54
        | exact resolve b0e54 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e13 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e13
        | (have j0 := b0e13 X1 X0
           have j1 := b0e14 X2 X0
           grind)
        | (have r₁ := b0e13 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e13 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e63 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63
      have b0e75 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e16
        | exact resolve b0e16 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : y = (τ y) := by
        first
        | (have i₁ := b0e11 y
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e11
        | exact resolve b0e11 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e107 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0
           have i₂ := b0e14 X1 X0
           grind)
        | exact superpose b0e14 b0e40
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e40 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e124 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ y = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e107 X0 X1
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e107
        | (have j0 := b0e107 X0 X1
           grind)
        | exact resolve b0e107 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107
      have b0e208 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e14 (τ X1) X0
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 X0 X0
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e262 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e696 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e262 y X0
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e262
        | exact resolve b0e262 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e262
      have b0e735 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e70 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e70 b0e15
        | (have j1 := b0e70 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e2431 : ∀ X0 X1 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 (σ X0)
           have i₂ := b0e67 X0 X1
           grind)
        | exact superpose b0e67 b0e40
        | (have j1 := b0e67 X0 X1
           grind)
        | exact resolve b0e40 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e67
      have b0e2458 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ y = (M.op (σ X0) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e2431 X0 X1
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e2431
        | (have j0 := b0e2431 X0 X1
           grind)
        | exact resolve b0e2431 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2431
      have b0e6517 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e208 X1 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e208
        | (have j0 := b0e208 X1 X1
           grind)
        | exact resolve b0e208 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e208
      have b0e6695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e6517 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e6517
        | (have j0 := b0e6517 X0 X1
           grind)
        | exact resolve b0e6517 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6517
      have b0e10468 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e735 x y X0
           grind)
        | exact superpose b0e735 b0e16
        | (have j1 := b0e735 x x X0
           grind)
        | exact resolve b0e16 b0e735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e735
      have b0e12905 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e2458 x y
           grind)
        | exact superpose b0e2458 b0e16
        | (have j1 := b0e2458 x x
           grind)
        | exact resolve b0e16 b0e2458
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2458
      have b0e72149 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e10468 X0
           have i₂ := b0e6695 y x
           grind)
        | exact superpose b0e6695 b0e10468
        | (have j0 := b0e10468 X0
           have j1 := b0e6695 X0 x
           grind)
        | (have r₁ := b0e10468 X0
           have r₂ := b0e6695 y x
           grind)
        | exact resolve b0e10468 b0e6695
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6695 b0e10468
      have b0e72151 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e72149 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72149
      have b0e72316 : (τ y) = (k y (τ (σ x))) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e696 (σ x)
           have i₂ := b0e72151 y
           grind)
        | exact superpose b0e72151 b0e696
        | exact resolve b0e696 b0e72151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e696 b0e72151
      have b0e72323 : (τ y) = (k y x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e72316
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e72316
        | exact resolve b0e72316 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72316
      have b0e72358 : y = (k y x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e72323
           have i₂ := b0e79
           grind)
        | exact superpose b0e79 b0e72323
        | exact resolve b0e72323 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79 b0e72323
      have b0e72367 : y = (k y x) := by
        first
        | (have j1 := b0e13 y x
           grind)
        | (have r₁ := b0e72358
           have r₂ := b0e13 x x
           grind)
        | exact resolve b0e72358 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72358
      have b0e72897 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e124 x y
           have i₂ := b0e72367
           grind)
        | exact superpose b0e72367 b0e124
        | (have j0 := b0e124 x x
           grind)
        | exact resolve b0e124 b0e72367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124
      have b0e72909 : y = (M.op x y) := by grind
      clear b0e72897
      have b0e72923 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e12905
           have i₂ := b0e72367
           grind)
        | exact superpose b0e72367 b0e12905
        | exact resolve b0e12905 b0e72367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12905 b0e72367
      have b0e72951 : y ≠ (σ (M.op x y)) ∨ y = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e72923
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e72923
        | exact resolve b0e72923 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72923
      have b0e72952 : y ≠ (σ y) ∨ y = (M.op (σ x) y) := by
        first
        | (have i₁ := b0e72951
           have i₂ := b0e72909
           grind)
        | exact superpose b0e72909 b0e72951
        | exact resolve b0e72951 b0e72909
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72951
      have b0e72953 : y = (M.op (σ x) y) := by
        first
        | (have r₁ := b0e72952
           have r₂ := b0e56
           grind)
        | exact resolve b0e72952 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72952
      have b0e73521 : (σ y) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e75
           have i₂ := b0e72909
           grind)
        | exact superpose b0e72909 b0e75
        | exact resolve b0e75 b0e72909
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75 b0e72909
      have b0e73624 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e73521
           have i₂ := b0e72953
           grind)
        | exact superpose b0e72953 b0e73521
        | exact resolve b0e73521 b0e72953
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72953 b0e73521
      have b0e73649 : False := by grind
      exact b0e73649
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 X0 y
           grind)
        | (have r₁ := b1e13 X0 y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e21 X0 y
           have i₂ := b1e20 (τ X0)
           grind)
        | exact superpose b1e20 b1e21
        | exact resolve b1e21 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e21
      have b1e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e56 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e28 X0
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e28
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e28 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e60 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e56 X0
           grind)
        | (have r₁ := b1e56 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e56 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e56 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56
      have b1e67 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e60 (σ y)
           grind)
        | exact superpose b1e60 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e60 (σ y)
           grind)
        | exact resolve b1e18 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60
      have b1e73 : False := by grind
      exact b1e73
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y y) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 X0 (σ y)
           grind)
        | (have r₁ := b2e13 X0 (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b2e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e24 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e20 (σ X0)
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e27 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e11 (k X0 y)
           have i₂ := b2e24 X0
           grind)
        | exact superpose b2e24 b2e11
        | exact resolve b2e11 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e28 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e27 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e27
        | exact resolve b2e27 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e55 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e28 X0
           have i₂ := b2e14 X0 y
           grind)
        | exact superpose b2e14 b2e28
        | (have j1 := b2e14 X0 y
           grind)
        | exact resolve b2e28 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e59 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e55 X0
           grind)
        | (have r₁ := b2e55 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e55 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e55 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55
      have b2e64 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e59 y
           grind)
        | exact superpose b2e59 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e59 y
           grind)
        | exact resolve b2e17 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59
      have b2e69 : False := by grind
      exact b2e69
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 x X1 X3
           have i₂ := b3e10 x X1 X0
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X1 x
           have i₂ := b3e10 X2 X1 x
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 X0
           have i₂ := b3e14 X2 X0
           grind)
        | exact superpose b3e14 b3e13
        | (have j0 := b3e13 X1 X0
           have j1 := b3e14 X2 X0
           grind)
        | (have r₁ := b3e13 X0 X1
           have r₂ := b3e14 X0 X1
           grind)
        | exact resolve b3e13 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e39 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 X0 (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 X0 (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e42 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b3e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e43 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e36 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e45 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e42 (σ X0)
           grind)
        | exact superpose b3e42 b3e15
        | exact resolve b3e15 b3e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X0 (τ X1))
           have i₂ := b3e20 X1 X0
           grind)
        | exact superpose b3e20 b3e11
        | exact resolve b3e11 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X1) = (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 (M.op X2 X2) X1 X3
           have i₂ := b3e23 X2 (M.op X1 (M.op X2 X2)) X0
           grind)
        | (have i₁ := b3e10 (M.op X2 X2) X1 X3
           have i₂ := b3e23 X0 (M.op X1 (M.op X2 X2)) X2
           grind)
        | exact superpose b3e23 b3e10
        | exact resolve b3e10 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23
      have b3e100 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e45 y
           grind)
        | exact superpose b3e45 b3e18
        | exact resolve b3e18 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e106 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op (σ X0) (σ (k X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 (σ X0) (σ y) X1
           have i₂ := b3e45 X0
           grind)
        | exact superpose b3e45 b3e10
        | exact resolve b3e10 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45
      have b3e161 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e100
           have i₂ := b3e43 y y X0
           grind)
        | exact superpose b3e43 b3e100
        | (have j1 := b3e43 y x X0
           grind)
        | exact resolve b3e100 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e100
      have b3e165 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e43 X0 X2 (τ X1)
           grind)
        | exact superpose b3e43 b3e19
        | (have j1 := b3e43 X0 X2 X2
           grind)
        | exact resolve b3e19 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e168 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e161 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e161
      have b3e247 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e168 (τ X0)
           grind)
        | exact superpose b3e168 b3e19
        | exact resolve b3e19 b3e168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e249 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e247 X0
           have i₂ := b3e42 X0
           grind)
        | exact superpose b3e42 b3e247
        | exact resolve b3e247 b3e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42 b3e247
      have b3e338 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e53 X0 X1
           have i₂ := b3e43 X1 (σ X0) X2
           grind)
        | exact superpose b3e43 b3e53
        | (have j1 := b3e43 X1 X1 X2
           grind)
        | exact resolve b3e53 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e43 b3e53
      have b3e350 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X2) = (k X2 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e338 X0 X1 X2
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e338
        | (have j0 := b3e338 X0 X1 X2
           grind)
        | exact resolve b3e338 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e338
      have b3e866 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e249 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e249
        | exact resolve b3e249 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e249
      have b3e1011 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e40 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40
      have b3e12525 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (τ (σ X0))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e350 X2 (σ X0) (σ X1)
           grind)
        | exact superpose b3e350 b3e15
        | (have j1 := b3e350 X2 (σ X0) X2
           grind)
        | exact resolve b3e15 b3e350
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e350
      have b3e12539 : ∀ X0 X1 X2 : G, (k X2 X0) = X2 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e12525 X0 X1 X2
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e12525
        | (have j0 := b3e12525 X0 X1 X2
           grind)
        | exact resolve b3e12525 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12525
      have b3e13619 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e165 X1 (σ X0) X2
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e165
        | (have j0 := b3e165 X1 X1 X2
           grind)
        | exact resolve b3e165 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e165
      have b3e13739 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13619 X0 X1 X2
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e13619
        | (have j0 := b3e13619 X0 X1 X2
           grind)
        | exact resolve b3e13619 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13619
      have b3e24329 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e1011 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e1011
        | (have j0 := b3e1011 (τ X0)
           grind)
        | exact resolve b3e1011 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e24358 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e24329 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e24329
        | (have j0 := b3e24329 X0
           grind)
        | exact resolve b3e24329 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24329
      have b3e24372 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e24358 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e24358
        | (have j0 := b3e24358 X0
           grind)
        | exact resolve b3e24358 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24358
      have b3e29919 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op y (k y y))) := by
        intro X0
        first
        | (have i₁ := b3e866 (k y y)
           have i₂ := b3e106 y X0
           grind)
        | exact superpose b3e106 b3e866
        | exact resolve b3e866 b3e106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e106 b3e866
      have b3e30016 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op y (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b3e29919 X0
           have i₂ := b3e168 y
           grind)
        | exact superpose b3e168 b3e29919
        | exact resolve b3e29919 b3e168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e168 b3e29919
      have b3e30726 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (σ (M.op X0 (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e30016 X1
           have i₂ := b3e26 y y X0
           grind)
        | (have i₁ := b3e30016 X1
           have i₂ := b3e26 X0 y y
           grind)
        | exact superpose b3e26 b3e30016
        | exact resolve b3e30016 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26 b3e30016
      have b3e36394 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e30726 (M.op x x) X1
           have i₂ := b3e95 x y x X0
           grind)
        | exact superpose b3e95 b3e30726
        | exact resolve b3e30726 b3e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e95 b3e30726
      have b3e48415 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X0) y)) = (σ (M.op (M.op X2 X2) y)) := by
        intro X0 X2
        first
        | (have i₁ := b3e36394 X2 x
           have i₂ := b3e36394 X0 x
           grind)
        | exact superpose b3e36394 b3e36394
        | exact resolve b3e36394 b3e36394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e422814 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e12539 x y X0
           grind)
        | exact superpose b3e12539 b3e16
        | (have j1 := b3e12539 x x X0
           grind)
        | exact resolve b3e16 b3e12539
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12539
      have b3e422882 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e422814 X0
           have j1 := b3e13739 X0 x X0
           grind)
        | (have r₁ := b3e422814 X0
           have r₂ := b3e13739 y x x
           grind)
        | exact resolve b3e422814 b3e13739
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13739 b3e422814
      have b3e424175 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e1011 x
           have i₂ := b3e422882 x
           grind)
        | exact superpose b3e422882 b3e1011
        | (have j0 := b3e1011 x
           grind)
        | exact resolve b3e1011 b3e422882
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1011
      have b3e424176 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e24372 x
           have i₂ := b3e422882 x
           grind)
        | exact superpose b3e422882 b3e24372
        | (have j0 := b3e24372 x
           grind)
        | (have r₁ := b3e24372 x
           have r₂ := b3e422882 x
           grind)
        | exact resolve b3e24372 b3e422882
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24372 b3e422882
      have b3e424250 : x = (M.op x x) := by grind
      clear b3e424176
      have b3e424251 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e424175
      have b3e426136 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0
        first
        | (have i₁ := b3e48415 x X0
           have i₂ := b3e424250
           grind)
        | exact superpose b3e424250 b3e48415
        | exact resolve b3e48415 b3e424250
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e48415 b3e424250
      have b3e436805 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op X0 X0) y)) := by
        intro X0
        first
        | (have i₁ := b3e36394 X0 (σ x)
           have i₂ := b3e424251
           grind)
        | exact superpose b3e424251 b3e36394
        | exact resolve b3e36394 b3e424251
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36394 b3e424251
      have b3e436931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e436805 x
           have i₂ := b3e426136 x
           grind)
        | exact superpose b3e426136 b3e436805
        | exact resolve b3e436805 b3e426136
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e426136 b3e436805
      have b3e437224 : False := by grind
      exact b3e437224

/-- `Equation4476`: `x ◇ (y ◇ y) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4476 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4476 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4476.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e20 : x = (k x y) := by grind
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      clear b0e23
      have b0e30 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e26 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e26
        | exact resolve b0e26 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (σ x) X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X0 X3 (M.op X2 X2)
           have i₂ := b0e10 X0 X2 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X0 X2) X3 X1
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) X0 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 x X0 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 x X0 X1
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e10
        | exact resolve b0e10 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X3) X2) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e14 X2 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X1) = X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (M.op X1 X1) X1 X2
           have i₂ := b0e14 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 (M.op X1 X1))
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 (M.op X1 X1) X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X2 X2)) ∨ (k X1 X0) = (M.op X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2 X1
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 X2)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e58 X0 X1 x
           have i₂ := b0e35 X1 X1 x X1
           grind)
        | exact superpose b0e35 b0e58
        | (have j0 := b0e58 X0 X1 x
           grind)
        | exact resolve b0e58 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e58
      have b0e67 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 y X0 x
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e10
        | exact resolve b0e10 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e67 X0
           have i₂ := b0e46 X0 y
           grind)
        | exact superpose b0e46 b0e67
        | exact resolve b0e67 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e67
      have b0e282 : (M.op y x) = (M.op y y) := by
        first
        | (have i₁ := b0e68 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e68
        | exact resolve b0e68 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e290 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e282
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e282
        | exact resolve b0e282 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e282
      have b0e496 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e38 y
           have i₂ := b0e290
           grind)
        | exact superpose b0e290 b0e38
        | exact resolve b0e38 b0e290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e547 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 (M.op X2 X2)) x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 X0 X2 X1 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e36
        | exact resolve b0e36 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e682 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e547 X0 X1 x
           have i₂ := b0e10 X0 x (M.op x x)
           grind)
        | exact superpose b0e10 b0e547
        | exact resolve b0e547 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e547
      have b0e729 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e682 X0 x
           have i₂ := b0e10 X0 y x
           grind)
        | exact superpose b0e10 b0e682
        | exact resolve b0e682 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e682
      have b0e755 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e729 X0
           have i₂ := b0e290
           grind)
        | exact superpose b0e290 b0e729
        | exact resolve b0e729 b0e290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e729
      have b0e762 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e755 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e755
        | exact resolve b0e755 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e755
      have b0e777 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) y)) := by grind
      clear b0e762
      have b0e810 : (M.op x y) = (k (M.op x y) (M.op x (M.op y y))) := by
        first
        | (have i₁ := b0e777
           have i₂ := b0e10 x y y
           grind)
        | exact superpose b0e10 b0e777
        | exact resolve b0e777 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e777
      have b0e832 : (M.op x y) = (k (M.op x y) (M.op y y)) := by
        first
        | (have i₁ := b0e810
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e810
        | exact resolve b0e810 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e810
      have b0e854 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e832
           have i₂ := b0e290
           grind)
        | exact superpose b0e290 b0e832
        | exact resolve b0e832 b0e290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e832
      have b0e1516 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (σ y)) ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X0 x
           have i₂ := b0e56 X1 X0 (σ x) x
           grind)
        | exact superpose b0e56 b0e32
        | (have j1 := b0e56 X1 X1 (σ x) x
           grind)
        | exact resolve b0e32 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e1810 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X2 (σ y)) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e32 X2 (M.op X1 X1)
           have i₂ := b0e59 X0 X2 X1
           grind)
        | exact superpose b0e59 b0e32
        | (have j1 := b0e59 X0 X2 X2
           grind)
        | exact resolve b0e32 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e1854 : ∀ X0 X2 : G, (M.op X0 (σ y)) = (M.op X2 (σ y)) ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e1810 X0 x X2
           have i₂ := b0e32 X0 x
           grind)
        | exact superpose b0e32 b0e1810
        | (have j0 := b0e1810 X0 x X2
           grind)
        | exact resolve b0e1810 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e1810
      have b0e3067 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e62 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e3142 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e65 X0 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e65
        | exact resolve b0e65 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e17233 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e3067 (M.op x y)
           have i₂ := b0e854
           grind)
        | exact superpose b0e854 b0e3067
        | (have j0 := b0e3067 (M.op x y)
           grind)
        | exact resolve b0e3067 b0e854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e854 b0e3067
      have b0e17249 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e17233
      have b0e25032 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e1854 X0 (σ x)
           grind)
        | (have i₁ := b0e16
           have i₂ := b0e1854 (σ x) x
           grind)
        | exact superpose b0e1854 b0e16
        | (have j1 := b0e1854 X0 (σ x)
           grind)
        | exact resolve b0e16 b0e1854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1854
      have b0e25586 : (σ y) = (M.op (σ y) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
        first
        | (have i₁ := b0e30 (σ y)
           have i₂ := b0e3142 (σ (M.op (τ (σ y)) (τ (σ y))))
           grind)
        | exact superpose b0e3142 b0e30
        | (have j1 := b0e3142 (σ (M.op (τ (σ y)) (τ (σ y))))
           grind)
        | exact resolve b0e30 b0e3142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e3142
      have b0e25656 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
        first
        | (have i₁ := b0e25586
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e25586
        | exact resolve b0e25586 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25586
      have b0e25675 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
        first
        | (have i₁ := b0e25656
           have i₂ := b0e290
           grind)
        | exact superpose b0e290 b0e25656
        | exact resolve b0e25656 b0e290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25656
      have b0e25686 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e25675
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e25675
        | exact resolve b0e25675 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25675
      have b0e25691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e25686
           have i₂ := b0e290
           grind)
        | exact superpose b0e290 b0e25686
        | exact resolve b0e25686 b0e290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e290 b0e25686
      have b0e25694 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
        first
        | (have r₁ := b0e25691
           have r₂ := b0e16
           grind)
        | exact resolve b0e25691 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25691
      have b0e34764 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e37 (σ (M.op x y))
           have i₂ := b0e17249
           grind)
        | exact superpose b0e17249 b0e37
        | exact resolve b0e37 b0e17249
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e34830 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e1516 (σ (M.op x y)) (σ (M.op x y))
           have i₂ := b0e17249
           grind)
        | exact superpose b0e17249 b0e1516
        | (have j0 := b0e1516 x (σ (M.op x y))
           grind)
        | exact resolve b0e1516 b0e17249
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1516 b0e17249
      have b0e34853 : (M.op (σ x) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
        first
        | (have j1 := b0e25032 (σ (M.op x y))
           grind)
        | (have r₁ := b0e34830
           have r₂ := b0e25032 (σ (M.op x y))
           grind)
        | exact resolve b0e34830 b0e25032
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25032 b0e34830
      have b0e34865 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e34764
           have i₂ := b0e25694
           grind)
        | exact superpose b0e25694 b0e34764
        | exact resolve b0e34764 b0e25694
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25694 b0e34764
      have b0e34872 : (M.op (σ x) (σ (M.op x y))) = (σ (k x (M.op x y))) := by
        first
        | (have i₁ := b0e34853
           have i₂ := b0e15 x (M.op x y)
           grind)
        | exact superpose b0e15 b0e34853
        | exact resolve b0e34853 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34853
      have b0e34875 : (σ y) = (σ (k x (M.op x y))) := by
        first
        | (have i₁ := b0e34872
           have i₂ := b0e34865
           grind)
        | exact superpose b0e34865 b0e34872
        | exact resolve b0e34872 b0e34865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34865 b0e34872
      have b0e36177 : (k x (M.op x y)) = (τ (σ y)) := by
        first
        | (have i₁ := b0e11 (k x (M.op x y))
           have i₂ := b0e34875
           grind)
        | exact superpose b0e34875 b0e11
        | exact resolve b0e11 b0e34875
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34875
      have b0e36213 : y = (k x (M.op x y)) := by
        first
        | (have i₁ := b0e36177
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e36177
        | exact resolve b0e36177 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36177
      have b0e37090 : y = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e14 x (M.op x y)
           have i₂ := b0e36213
           grind)
        | exact superpose b0e36213 b0e14
        | (have j0 := b0e14 x (M.op x y)
           grind)
        | exact resolve b0e14 b0e36213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37113 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e37090
           have i₂ := b0e496
           grind)
        | exact superpose b0e496 b0e37090
        | exact resolve b0e37090 b0e496
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e496 b0e37090
      have b0e37135 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e37113
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e37113
        | exact resolve b0e37113 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37113
      have b0e37136 : y = (M.op x y) := by grind
      clear b0e37135
      have b0e37705 : y = (k x y) := by
        first
        | (have i₁ := b0e36213
           have i₂ := b0e37136
           grind)
        | exact superpose b0e37136 b0e36213
        | exact resolve b0e36213 b0e37136
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36213 b0e37136
      have b0e37767 : x = y := by
        first
        | (have i₁ := b0e37705
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e37705
        | exact resolve b0e37705 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e37705
      have b0e39693 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e37767
           grind)
        | exact superpose b0e37767 b0e16
        | exact resolve b0e16 b0e37767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37767
      have b0e39774 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e39693
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e39693
        | exact resolve b0e39693 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39693
      have b0e39778 : False := by grind
      exact b0e39778
    · have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : x = (k x y) := by grind
      have b1e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e55 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 (σ x) X0
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 (σ x) X0
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 (σ x) (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e69 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e22 X1 X0
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22
      have b1e173 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e51 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e319 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e55 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e320 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e319
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e319
        | exact resolve b1e319 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e319
      have b1e321 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e320
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e320
        | exact resolve b1e320 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e320
      have b1e503 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e321
           grind)
        | exact superpose b1e321 b1e16
        | exact resolve b1e16 b1e321
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e321
      have b1e2244 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e69
      have b1e2262 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e2244 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e2244
        | exact resolve b1e2244 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2244
      have b1e2291 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e56 x x
           grind)
        | exact superpose b1e56 b1e18
        | (have j1 := b1e56 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e56 x y
           grind)
        | exact resolve b1e18 b1e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56
      have b1e2400 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e173 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e173
        | (have j0 := b1e173 x x
           grind)
        | exact resolve b1e173 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e173
      have b1e18981 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e2291
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e2291
        | (have j1 := b1e14 (σ x) (σ x)
           grind)
        | exact resolve b1e2291 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2291
      have b1e18997 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e18981
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e18981
        | exact resolve b1e18981 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18981
      have b1e18998 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e18997
      have b1e19007 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e18998
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e18998
        | exact resolve b1e18998 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18998
      have b1e19014 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e2262 x
           have i₂ := b1e19007
           grind)
        | exact superpose b1e19007 b1e2262
        | exact resolve b1e2262 b1e19007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2262 b1e19007
      have b1e19097 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e19014
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e19014
        | exact resolve b1e19014 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19014
      have b1e19100 : x = (k x x) := by
        first
        | (have r₁ := b1e19097
           have r₂ := b1e2400
           grind)
        | exact resolve b1e19097 b1e2400
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2400 b1e19097
      have b1e19122 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e19100
           grind)
        | exact superpose b1e19100 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e19100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19100
      have b1e19127 : x = (M.op x x) := by grind
      clear b1e19122
      have b1e19174 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e19127
           grind)
        | exact superpose b1e19127 b1e17
        | exact resolve b1e17 b1e19127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19127
      have b1e19740 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e503
           have i₂ := b1e19174
           grind)
        | exact superpose b1e19174 b1e503
        | exact resolve b1e503 b1e19174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e503
      have b1e19763 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e19740
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e19740
        | exact resolve b1e19740 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19740
      have b1e19771 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e19763
           have i₂ := b1e19174
           grind)
        | exact superpose b1e19174 b1e19763
        | exact resolve b1e19763 b1e19174
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19174 b1e19763
      have b1e19772 : False := by grind
      exact b1e19772
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x x) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ x) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e20
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e20
        | exact resolve b2e20 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e26 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e21
           grind)
        | exact superpose b2e21 b2e11
        | exact resolve b2e11 b2e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e27 : x = (k x y) := by
        first
        | (have i₁ := b2e26
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e26
        | exact resolve b2e26 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e26
      have b2e52 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e59 : x = (M.op x y) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e27
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e27
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e27 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e62 : x = (M.op x y) := by
        first
        | (have r₁ := b2e59
           have r₂ := b2e17
           grind)
        | exact resolve b2e59 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59
      have b2e2809 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e57 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e57
        | exact resolve b2e57 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e3586 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e2809
           grind)
        | exact superpose b2e2809 b2e11
        | exact resolve b2e11 b2e2809
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2809
      have b2e3602 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e3586
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e3586
        | exact resolve b2e3586 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3586
      have b2e4233 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e52 x x
           have i₂ := b2e3602
           grind)
        | exact superpose b2e3602 b2e52
        | exact resolve b2e52 b2e3602
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52 b2e3602
      have b2e4236 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e4233
           have r₂ := b2e17
           grind)
        | exact resolve b2e4233 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4233
      have b2e4492 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e4236
           grind)
        | exact superpose b2e4236 b2e11
        | exact resolve b2e11 b2e4236
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4236
      have b2e4508 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e4492
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e4492
        | exact resolve b2e4492 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4492
      have b2e4509 : x = y := by grind
      clear b2e4508
      have b2e5111 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e4509
           grind)
        | exact superpose b2e4509 b2e16
        | exact resolve b2e16 b2e4509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e5115 : x = (M.op x x) := by
        first
        | (have i₁ := b2e62
           have i₂ := b2e4509
           grind)
        | exact superpose b2e4509 b2e62
        | exact resolve b2e62 b2e4509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62
      have b2e5123 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e5111
           have i₂ := b2e5115
           grind)
        | exact superpose b2e5115 b2e5111
        | exact resolve b2e5111 b2e5115
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5111 b2e5115
      have b2e5124 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e5123
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e5123
        | exact resolve b2e5123 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5123
      have b2e5125 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e5124
           have i₂ := b2e4509
           grind)
        | exact superpose b2e4509 b2e5124
        | exact resolve b2e5124 b2e4509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4509 b2e5124
      have b2e5126 : False := by grind
      exact b2e5126
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e44 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e212 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e44 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44
      have b3e213 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e212
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e212
        | exact resolve b3e212 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e212
      have b3e339 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e213
           grind)
        | exact superpose b3e213 b3e16
        | exact resolve b3e16 b3e213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e213
      have b3e414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e339
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e339
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e339 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e339
      have b3e415 : y = (M.op x x) := by grind
      clear b3e414
      have b3e417 : False := by grind
      exact b3e417

/-- `Equation4476`: `x ◇ (y ◇ y) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4476 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4476 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4476.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op x x) := by grind
        have b0e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 (σ x) X1
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e11 x X0 x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e49 : y = (M.op x y) := by
          first
          | (have i₁ := b0e41 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e41
          | exact resolve b0e41 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e65 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b0e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X1 X0
             have i₂ := b0e15 (σ X1) (σ X0)
             grind)
          | exact superpose b0e15 b0e16
          | (have j1 := b0e15 (σ X1) (σ X0)
             grind)
          | exact resolve b0e16 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e295 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b0e65 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e65
        have b0e1570 : y ≠ y ∨ y = (k y x) := by
          first
          | (have i₁ := b0e295 y x
             have i₂ := b0e49
             grind)
          | exact superpose b0e49 b0e295
          | (have j0 := b0e295 y x
             grind)
          | (have r₁ := b0e295 y x
             have r₂ := b0e49
             grind)
          | exact resolve b0e295 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e295
        have b0e1576 : y = (k y x) := by grind
        clear b0e1570
        have b0e2755 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e70 x y
             grind)
          | exact superpose b0e70 b0e17
          | (have j1 := b0e70 x y
             grind)
          | exact resolve b0e17 b0e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e70
        have b0e2840 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e2755
             have i₂ := b0e1576
             grind)
          | exact superpose b0e1576 b0e2755
          | exact resolve b0e2755 b0e1576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1576 b0e2755
        have b0e2852 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e2840
             have i₂ := b0e49
             grind)
          | exact superpose b0e49 b0e2840
          | exact resolve b0e2840 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2840
        have b0e2853 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear b0e2852
        have b0e2875 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e35 (σ y) (σ y)
             have i₂ := b0e2853
             grind)
          | exact superpose b0e2853 b0e35
          | exact resolve b0e35 b0e2853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e35
        have b0e2893 : (σ x) = (σ y) := by
          first
          | (have i₁ := b0e2875
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e2875
          | exact resolve b0e2875 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2875
        have b0e3129 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e2893
             grind)
          | exact superpose b0e2893 b0e17
          | exact resolve b0e17 b0e2893
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e3151 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b0e3129
             have i₂ := b0e2853
             grind)
          | exact superpose b0e2853 b0e3129
          | exact resolve b0e3129 b0e2853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2853 b0e3129
        have b0e3155 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e3151
             have i₂ := b0e2893
             grind)
          | exact superpose b0e2893 b0e3151
          | exact resolve b0e3151 b0e2893
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2893 b0e3151
        have b0e3159 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e3155
             have i₂ := b0e49
             grind)
          | exact superpose b0e49 b0e3155
          | exact resolve b0e3155 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e49 b0e3155
        have b0e3160 : False := by grind
        exact b0e3160
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op x x) := by grind
        have b1e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b1e20 : y ≠ (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 (σ x) X1
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X0 X2 X3
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X0 X3 (M.op X2 X2)
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e11 (σ x) X0 (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e11 x X0 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e34 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e34
          | exact resolve b1e34 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 x X0 X1
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e11
          | exact resolve b1e11 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 x X1 (M.op X0 X0)
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e11
          | exact resolve b1e11 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e43 X0 X1
             have i₂ := b1e34 X1
             grind)
          | exact superpose b1e34 b1e43
          | exact resolve b1e43 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e43
        have b1e54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X1) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 (M.op X1 X1) X1 X2
             have i₂ := b1e15 (M.op X1 X1) X0
             grind)
          | (have i₁ := b1e11 X0 X1 X2
             have i₂ := b1e15 X0 (M.op X0 (M.op X1 X1))
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 (M.op X1 X1) X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e54 X0 X1 x
             have i₂ := b1e31 X1 X1 x X1
             grind)
          | exact superpose b1e31 b1e54
          | (have j0 := b1e54 X0 X1 x
             grind)
          | exact resolve b1e54 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e54
        have b1e65 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b1e25
        have b1e70 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e65 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e65
          | exact resolve b1e65 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e95 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) (M.op X2 X2)) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 (M.op x X1) X2 X0
             have i₂ := b1e42 X0 X1
             grind)
          | exact superpose b1e42 b1e11
          | exact resolve b1e11 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e96 : ∀ X1 X2 : G, (M.op y X2) = (M.op (M.op x X1) (M.op X2 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b1e95 x X1 X2
             have i₂ := b1e44 x X2
             grind)
          | exact superpose b1e44 b1e95
          | exact resolve b1e95 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e95
        have b1e100 : ∀ X2 : G, (M.op y X2) = (M.op y (M.op X2 X2)) := by
          intro X2
          first
          | (have i₁ := b1e96 x X2
             have i₂ := b1e42 (M.op X2 X2) x
             grind)
          | exact superpose b1e42 b1e96
          | exact resolve b1e96 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e96
        have b1e101 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 X1) X2) (σ x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28 X0 (M.op X2 X2)
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e28
          | exact resolve b1e28 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e106 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e28 (σ x) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e28
          | exact resolve b1e28 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e121 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e101 X0 X1 x
             have i₂ := b1e28 (M.op X0 X1) x
             grind)
          | exact superpose b1e28 b1e101
          | exact resolve b1e101 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e101
        have b1e201 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X2) (M.op (M.op X0 X1) (M.op X0 X2))) := by
          intro X0 X1 X2
          grind
        clear b1e29
        have b1e238 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b1e100 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e100
          | exact resolve b1e100 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100
        have b1e3020 : ∀ X0 : G, (M.op (σ y) (σ x)) = X0 ∨ (M.op X0 (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e33 (σ x)
             have i₂ := b1e60 X0 (σ x)
             grind)
          | (have i₁ := b1e33 X0
             have i₂ := b1e60 (M.op (σ x) (M.op X0 X0)) x
             grind)
          | exact superpose b1e60 b1e33
          | (have j1 := b1e60 X0 (σ x)
             grind)
          | exact resolve b1e33 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e60
        have b1e3026 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op (σ y) (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3020 X0
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e3020
          | (have j0 := b1e3020 X0
             grind)
          | exact resolve b1e3020 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3020
        have b1e3177 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e106
             grind)
          | exact superpose b1e106 b1e17
          | exact resolve b1e17 b1e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e3199 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e3177
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e3177
          | exact resolve b1e3177 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e3177
        have b1e3204 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e3199
             have i₂ := b1e238
             grind)
          | exact superpose b1e238 b1e3199
          | exact resolve b1e3199 b1e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e238 b1e3199
        have b1e23815 : (σ y) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
          first
          | (have i₁ := b1e70 (σ y)
             have i₂ := b1e3026 (σ (M.op (τ (σ y)) (τ (σ y))))
             grind)
          | exact superpose b1e3026 b1e70
          | (have j1 := b1e3026 (σ (M.op (τ (σ y)) (τ (σ y))))
             grind)
          | exact resolve b1e70 b1e3026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e3026
        have b1e23863 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
          first
          | (have i₁ := b1e23815
             have i₂ := b1e12 y
             grind)
          | exact superpose b1e12 b1e23815
          | exact resolve b1e23815 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23815
        have b1e23885 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have i₁ := b1e23863
             have i₂ := b1e12 y
             grind)
          | exact superpose b1e12 b1e23863
          | exact resolve b1e23863 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23863
        have b1e23894 : (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have r₁ := b1e23885
             have r₂ := b1e3204
             grind)
          | exact resolve b1e23885 b1e3204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3204 b1e23885
        have b1e23932 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (M.op (σ (M.op y y)) X0) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e201 (σ (M.op y y)) x (σ y)
             have i₂ := b1e23894
             grind)
          | exact superpose b1e23894 b1e201
          | exact resolve b1e201 b1e23894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e201
        have b1e23950 : (σ y) = (k (σ y) (M.op (σ (M.op y y)) (σ y))) := by
          first
          | (have i₁ := b1e23932 x
             have i₂ := b1e121 (σ (M.op y y)) x
             grind)
          | exact superpose b1e121 b1e23932
          | exact resolve b1e23932 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121 b1e23932
        have b1e23964 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e23950
             have i₂ := b1e23894
             grind)
          | exact superpose b1e23894 b1e23950
          | exact resolve b1e23950 b1e23894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23894 b1e23950
        have b1e23968 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e23964
             have i₂ := b1e16 y y
             grind)
          | exact superpose b1e16 b1e23964
          | exact resolve b1e23964 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23964
        have b1e24183 : (τ (σ y)) = (k y y) := by
          first
          | (have i₁ := b1e12 (k y y)
             have i₂ := b1e23968
             grind)
          | exact superpose b1e23968 b1e12
          | exact resolve b1e12 b1e23968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23968
        have b1e24217 : y = (k y y) := by
          first
          | (have i₁ := b1e24183
             have i₂ := b1e12 y
             grind)
          | exact superpose b1e12 b1e24183
          | exact resolve b1e24183 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24183
        have b1e25760 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e24217
             grind)
          | exact superpose b1e24217 b1e15
          | (have j0 := b1e15 y y
             grind)
          | exact resolve b1e15 b1e24217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24217
        have b1e25765 : y = (M.op y y) := by grind
        clear b1e25760
        have b1e25771 : False := by grind
        exact b1e25771
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e23 : y = (k y y) := by grind
        have b2e37 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e11 x X0 x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e11
          | exact resolve b2e11 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : y = (M.op x y) := by
          first
          | (have i₁ := b2e37 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e37
          | exact resolve b2e37 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 X0
             have i₂ := b2e15 (σ X1) (σ X0)
             grind)
          | exact superpose b2e15 b2e16
          | (have j1 := b2e15 (σ X1) (σ X0)
             grind)
          | exact resolve b2e16 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e199 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e59 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e645 : y ≠ y ∨ y = (k y x) := by
          first
          | (have i₁ := b2e199 y x
             have i₂ := b2e44
             grind)
          | exact superpose b2e44 b2e199
          | (have j0 := b2e199 y x
             grind)
          | (have r₁ := b2e199 y x
             have r₂ := b2e44
             grind)
          | exact resolve b2e199 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e199
        have b2e650 : y = (k y x) := by grind
        clear b2e645
        have b2e2290 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e17
             have i₂ := b2e64 x y
             grind)
          | exact superpose b2e64 b2e17
          | (have j1 := b2e64 x y
             grind)
          | exact resolve b2e17 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2371 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e2290
             have i₂ := b2e650
             grind)
          | exact superpose b2e650 b2e2290
          | exact resolve b2e2290 b2e650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e650 b2e2290
        have b2e2382 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e2371
             have i₂ := b2e44
             grind)
          | exact superpose b2e44 b2e2371
          | exact resolve b2e2371 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44 b2e2371
        have b2e2383 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear b2e2382
        have b2e2393 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e64 y y
             have i₂ := b2e2383
             grind)
          | exact superpose b2e2383 b2e64
          | exact resolve b2e64 b2e2383
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e2430 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e2393
             have i₂ := b2e23
             grind)
          | exact superpose b2e23 b2e2393
          | exact resolve b2e2393 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e2393
        have b2e2431 : (σ x) = (σ y) := by grind
        clear b2e2430
        have b2e2655 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e2431
             grind)
          | exact superpose b2e2431 b2e19
          | exact resolve b2e19 b2e2431
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2673 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e2655
             have i₂ := b2e2383
             grind)
          | exact superpose b2e2383 b2e2655
          | exact resolve b2e2655 b2e2383
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2383 b2e2655
        have b2e2678 : False := by grind
        exact b2e2678
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op x x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 (τ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e16
          | exact resolve b3e16 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e11 x X0 x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e11 x X0 X1
             have i₂ := b3e28 X0
             grind)
          | exact superpose b3e28 b3e11
          | exact resolve b3e11 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e11 x X1 (M.op X0 X0)
             have i₂ := b3e28 X0
             grind)
          | exact superpose b3e28 b3e11
          | exact resolve b3e11 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e38 X0 X1
             have i₂ := b3e28 X1
             grind)
          | exact superpose b3e28 b3e38
          | exact resolve b3e38 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op x X0) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e28 X1
             have i₂ := b3e15 X1 X0
             grind)
          | (have i₁ := b3e28 X0
             have i₂ := b3e15 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e15 b3e28
          | (have j1 := b3e15 X1 X0
             grind)
          | exact resolve b3e28 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e15 (σ X1) (σ X0)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X1) (σ X0)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e77 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) (M.op X2 X2)) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 (M.op x X1) X2 X0
             have i₂ := b3e37 X0 X1
             grind)
          | exact superpose b3e37 b3e11
          | exact resolve b3e11 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : ∀ X1 X2 : G, (M.op y X2) = (M.op (M.op x X1) (M.op X2 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b3e77 x X1 X2
             have i₂ := b3e39 x X2
             grind)
          | exact superpose b3e39 b3e77
          | exact resolve b3e77 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e77
        have b3e82 : ∀ X2 : G, (M.op y X2) = (M.op y (M.op X2 X2)) := by
          intro X2
          first
          | (have i₁ := b3e78 x X2
             have i₂ := b3e37 (M.op X2 X2) x
             grind)
          | exact superpose b3e37 b3e78
          | exact resolve b3e78 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e78
        have b3e89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (k X0 (τ X1))
             have i₂ := b3e24 X1 X0
             grind)
          | exact superpose b3e24 b3e12
          | exact resolve b3e12 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e171 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b3e82 x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e82
          | exact resolve b3e82 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e1173 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b3e89
        have b3e1188 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e1173 X0
             have i₂ := b3e12 X0
             grind)
          | exact superpose b3e12 b3e1173
          | exact resolve b3e1173 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1173
        have b3e2215 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e53 x x
             grind)
          | exact superpose b3e53 b3e19
          | (have j1 := b3e53 x x
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e53 y x
             grind)
          | exact resolve b3e19 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e18519 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e2215
             have i₂ := b3e45 x x
             grind)
          | exact superpose b3e45 b3e2215
          | (have j1 := b3e45 x x
             grind)
          | exact resolve b3e2215 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e2215
        have b3e18526 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e18519
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e18519
          | exact resolve b3e18519 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18519
        have b3e18527 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y x) := by grind
        clear b3e18526
        have b3e18541 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e18527
             have i₂ := b3e171
             grind)
          | exact superpose b3e171 b3e18527
          | exact resolve b3e18527 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171 b3e18527
        have b3e18545 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e18541
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e18541
          | exact resolve b3e18541 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18541
        have b3e18548 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b3e18545
             have r₂ := b3e20
             grind)
          | exact resolve b3e18545 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18545
        have b3e18555 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e18548
             grind)
          | exact superpose b3e18548 b3e19
          | exact resolve b3e19 b3e18548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e18557 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b3e1188 x
             have i₂ := b3e18548
             grind)
          | exact superpose b3e18548 b3e1188
          | exact resolve b3e1188 b3e18548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1188 b3e18548
        have b3e18637 : x = (k x x) := by
          first
          | (have i₁ := b3e18557
             have i₂ := b3e12 x
             grind)
          | exact superpose b3e12 b3e18557
          | exact resolve b3e18557 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18557
        have b3e18698 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e18637
             grind)
          | exact superpose b3e18637 b3e15
          | (have j0 := b3e15 x x
             grind)
          | exact resolve b3e15 b3e18637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18637
        have b3e18703 : x = (M.op x x) := by grind
        clear b3e18698
        have b3e18710 : x = y := by
          first
          | (have i₁ := b3e18703
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e18703
          | exact resolve b3e18703 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18703
        have b3e19227 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e18555
             have i₂ := b3e18710
             grind)
          | exact superpose b3e18710 b3e18555
          | exact resolve b3e18555 b3e18710
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18555 b3e18710
        have b3e19229 : False := by grind
        exact b3e19229
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op x x) := by grind
        have b4e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b4e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e23 : (σ x) = (k (σ x) (σ y)) := by grind
        have b4e24 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e23
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e23
          | exact resolve b4e23 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e23
        have b4e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 (τ X0) X1
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e16
          | exact resolve b4e16 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e29 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e24
             grind)
          | exact superpose b4e24 b4e12
          | exact resolve b4e12 b4e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e30 : x = (k x y) := by
          first
          | (have i₁ := b4e29
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e29
          | exact resolve b4e29 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e29
        have b4e40 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b4e11 y X0 y
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e64 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b4e19
             have i₂ := b4e15 (σ x) X0
             grind)
          | (have i₁ := b4e19
             have i₂ := b4e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b4e15 b4e19
          | (have j1 := b4e15 (σ x) X0
             grind)
          | exact resolve b4e19 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e66 : x = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e30
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e30
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e30 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e30
        have b4e67 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e24
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e24
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e24 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e71 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b4e67
             have r₂ := b4e18
             grind)
          | exact resolve b4e67 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e67
        have b4e72 : x = (M.op y x) := by
          first
          | (have r₁ := b4e66
             have r₂ := b4e18
             grind)
          | exact resolve b4e66 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e66
        have b4e76 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b4e11 y X0 x
             have i₂ := b4e72
             grind)
          | exact superpose b4e72 b4e11
          | exact resolve b4e11 b4e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e77 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b4e76 X0
             have i₂ := b4e40 X0
             grind)
          | exact superpose b4e40 b4e76
          | exact resolve b4e76 b4e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e40 b4e76
        have b4e79 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b4e25
        have b4e84 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b4e79 X0
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e79
          | exact resolve b4e79 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e79
        have b4e101 : y ≠ (M.op y x) := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e77 x
             grind)
          | exact superpose b4e77 b4e18
          | exact resolve b4e18 b4e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e110 : x ≠ y := by
          first
          | (have i₁ := b4e101
             have i₂ := b4e72
             grind)
          | exact superpose b4e72 b4e101
          | exact resolve b4e101 b4e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e72 b4e101
        have b4e808 : (σ x) = (M.op (σ (M.op (τ (σ x)) (τ (σ x)))) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e64 (σ (M.op (τ (σ x)) (τ (σ x))))
             have i₂ := b4e84 (σ x)
             grind)
          | exact superpose b4e84 b4e64
          | (have j0 := b4e64 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b4e64 b4e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e64 b4e84
        have b4e811 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e808
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e808
          | exact resolve b4e808 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e808
        have b4e818 : (σ x) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e811
             have i₂ := b4e77 x
             grind)
          | exact superpose b4e77 b4e811
          | exact resolve b4e811 b4e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e811
        have b4e821 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e818
             have i₂ := b4e71
             grind)
          | exact superpose b4e71 b4e818
          | exact resolve b4e818 b4e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e818
        have b4e823 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
          first
          | (have i₁ := b4e821
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e821
          | exact resolve b4e821 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e821
        have b4e825 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e823
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e823
          | exact resolve b4e823 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e823
        have b4e827 : (σ y) = (σ (M.op y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e825
             have i₂ := b4e77 x
             grind)
          | exact superpose b4e77 b4e825
          | exact resolve b4e825 b4e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e77 b4e825
        have b4e829 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e827
             have i₂ := b4e71
             grind)
          | exact superpose b4e71 b4e827
          | exact resolve b4e827 b4e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e71 b4e827
        have b4e830 : (σ x) = (σ y) := by grind
        clear b4e829
        have b4e1166 : x = (τ (σ y)) := by
          first
          | (have i₁ := b4e12 x
             have i₂ := b4e830
             grind)
          | exact superpose b4e830 b4e12
          | exact resolve b4e12 b4e830
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e830
        have b4e1167 : x = y := by
          first
          | (have i₁ := b4e1166
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e1166
          | exact resolve b4e1166 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1166
        have b4e1172 : False := by grind
        exact b4e1172
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op x x) := by grind
        have b5e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b5e20 : y ≠ (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        have b5e23 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e22
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e22
          | exact resolve b5e22 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22
        have b5e24 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b5e12 (k x y)
             have i₂ := b5e23
             grind)
          | exact superpose b5e23 b5e12
          | exact resolve b5e12 b5e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e25 : x = (k x y) := by
          first
          | (have i₁ := b5e24
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e24
          | exact resolve b5e24 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X1 X0
             have i₂ := b5e15 (σ X1) (σ X0)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X1) (σ X0)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e70 : x = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b5e25
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e25
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e25 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e73 : x = (M.op y x) := by
          first
          | (have r₁ := b5e70
             have r₂ := b5e18
             grind)
          | exact resolve b5e70 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e70
        have b5e2651 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e68 x x
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e68
          | exact resolve b5e68 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e68
        have b5e4132 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (k x x)
             have i₂ := b5e2651
             grind)
          | exact superpose b5e2651 b5e12
          | exact resolve b5e12 b5e2651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2651
        have b5e4145 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e4132
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e4132
          | exact resolve b5e4132 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e4132
        have b5e4152 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e62 x x
             have i₂ := b5e4145
             grind)
          | exact superpose b5e4145 b5e62
          | exact resolve b5e62 b5e4145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62 b5e4145
        have b5e4155 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b5e4152
             have r₂ := b5e18
             grind)
          | exact resolve b5e4152 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e4152
        have b5e4838 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b5e12 x
             have i₂ := b5e4155
             grind)
          | exact superpose b5e4155 b5e12
          | exact resolve b5e12 b5e4155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e4155
        have b5e4851 : x = y ∨ x = y := by
          first
          | (have i₁ := b5e4838
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e4838
          | exact resolve b5e4838 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e4838
        have b5e4852 : x = y := by grind
        clear b5e4851
        have b5e5126 : y = (M.op y y) := by
          first
          | (have i₁ := b5e73
             have i₂ := b5e4852
             grind)
          | exact superpose b5e4852 b5e73
          | exact resolve b5e73 b5e4852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e73 b5e4852
        have b5e5133 : False := by grind
        exact b5e5133
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b6e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b6e20 : y = (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e22 : y = (k y y) := by grind
        have b6e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 (τ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e16
          | exact resolve b6e16 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e15 (σ X1) (σ X0)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X1) (σ X0)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e81 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X0 X1
             have i₂ := b6e15 X1 (τ X0)
             grind)
          | exact superpose b6e15 b6e24
          | (have j1 := b6e15 X1 (τ X0)
             grind)
          | exact resolve b6e24 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e1986 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e53 x y
             grind)
          | exact superpose b6e53 b6e17
          | (have j1 := b6e53 x y
             grind)
          | exact resolve b6e17 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2048 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e53 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e17403 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e2048 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2048
          | (have j0 := b6e2048 y
             grind)
          | exact resolve b6e2048 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22 b6e2048
        have b6e17408 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e17403
        have b6e17484 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e81 (σ X0) X1
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e81
          | exact resolve b6e81 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e17725 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e17484 X0 X1
             have i₂ := b6e16 X1 X0
             grind)
          | exact superpose b6e16 b6e17484
          | (have j0 := b6e17484 X0 X1
             grind)
          | exact resolve b6e17484 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17484
        have b6e34889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e1986
             have i₂ := b6e17725 x y
             grind)
          | exact superpose b6e17725 b6e1986
          | (have j1 := b6e17725 (σ x) (σ y)
             grind)
          | (have r₁ := b6e1986
             have r₂ := b6e17725 x y
             grind)
          | exact resolve b6e1986 b6e17725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1986 b6e17725
        have b6e34890 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b6e34889
        have b6e34901 : (σ x) = (σ y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e34890
             have i₂ := b6e17408
             grind)
          | exact superpose b6e17408 b6e34890
          | exact resolve b6e34890 b6e17408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34890
        have b6e34912 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e34901
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e34901
          | exact resolve b6e34901 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34901
        have b6e34919 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b6e12 x
             have i₂ := b6e34912
             grind)
          | exact superpose b6e34912 b6e12
          | exact resolve b6e12 b6e34912
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34912
        have b6e34957 : x = y ∨ x = y := by
          first
          | (have i₁ := b6e34919
             have i₂ := b6e12 y
             grind)
          | exact superpose b6e12 b6e34919
          | exact resolve b6e34919 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34919
        have b6e34958 : x = y := by grind
        clear b6e34957
        have b6e35059 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e34958
             grind)
          | exact superpose b6e34958 b6e19
          | exact resolve b6e19 b6e34958
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34958
        have b6e35077 : False := by grind
        exact b6e35077
      · have b7e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b7e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b7e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b7e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op x x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b7e20 : y ≠ (M.op y y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 (τ X0) X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e16
          | exact resolve b7e16 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e16
          | exact resolve b7e16 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 (k (τ X0) X1)
             have i₂ := b7e22 X0 X1
             grind)
          | exact superpose b7e22 b7e12
          | exact resolve b7e12 b7e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X0)) = (M.op X2 (M.op (M.op (M.op X0 X0) X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X2 (M.op X0 X0) X3
             have i₂ := b7e11 (M.op X0 X0) X0 X1
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 X2 X3
             have i₂ := b7e11 X0 X2 X1
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X0 X3 (M.op X2 X2)
             have i₂ := b7e11 X0 X2 X1
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 (M.op X0 X2) X3 X1
             have i₂ := b7e11 X0 X1 X2
             grind)
          | exact superpose b7e11 b7e11
          | exact resolve b7e11 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e36 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X0)) := by
          intro X0 X1
          grind
        have b7e37 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X0)) = (M.op X2 (M.op X0 (M.op X0 X0))) := by
          intro X0 X2 X3
          first
          | (have i₁ := b7e30 X0 x X2 X3
             have i₂ := b7e33 X0 X0 x X0
             grind)
          | exact superpose b7e33 b7e30
          | exact resolve b7e30 b7e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e30
        have b7e43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 (k X0 (τ X1))
             have i₂ := b7e23 X1 X0
             grind)
          | exact superpose b7e23 b7e12
          | exact resolve b7e12 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e49 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X3) X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X1 X2 X3
             have i₂ := b7e15 X2 X0
             grind)
          | (have i₁ := b7e11 X0 X1 X2
             have i₂ := b7e15 X0 (M.op X1 X1)
             grind)
          | exact superpose b7e15 b7e11
          | (have j1 := b7e15 X2 X0
             grind)
          | exact resolve b7e11 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e51 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X1) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e11 (M.op X1 X1) X1 X2
             have i₂ := b7e15 (M.op X1 X1) X0
             grind)
          | (have i₁ := b7e11 X0 X1 X2
             have i₂ := b7e15 X0 (M.op X0 (M.op X1 X1))
             grind)
          | exact superpose b7e15 b7e11
          | (have j1 := b7e15 (M.op X1 X1) X0
             grind)
          | exact resolve b7e11 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e52 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X2 X2)) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e11 X1 X2 X1
             have i₂ := b7e15 X1 X0
             grind)
          | (have i₁ := b7e11 X0 X1 X2
             have i₂ := b7e15 X0 (M.op X0 X2)
             grind)
          | exact superpose b7e15 b7e11
          | (have j1 := b7e15 X1 X0
             grind)
          | exact resolve b7e11 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b7e19
             have i₂ := b7e15 (σ x) X0
             grind)
          | (have i₁ := b7e19
             have i₂ := b7e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b7e15 b7e19
          | (have j1 := b7e15 (σ x) X0
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e15 (σ x) (σ y)
             grind)
          | exact resolve b7e19 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e23 X0 X1
             have i₂ := b7e15 X1 (τ X0)
             grind)
          | exact superpose b7e15 b7e23
          | (have j1 := b7e15 X1 (τ X0)
             grind)
          | exact resolve b7e23 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 X0
             have i₂ := b7e15 (σ X1) (σ X0)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X1) (σ X0)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e58 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e51 X0 X1 x
             have i₂ := b7e33 X1 X1 x X1
             grind)
          | exact superpose b7e33 b7e51
          | (have j0 := b7e51 X0 X1 x
             grind)
          | exact resolve b7e51 b7e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e51
        have b7e60 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e28 X1 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e28
          | exact resolve b7e28 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e79 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X0 X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e31 X0 X3 X4 (M.op X2 X2)
             have i₂ := b7e11 X0 X2 X1
             grind)
          | exact superpose b7e11 b7e31
          | exact resolve b7e31 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e50 (σ X1) (σ X0)
             have i₂ := b7e16 X0 X1
             grind)
          | exact superpose b7e16 b7e50
          | exact resolve b7e50 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e123 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b7e50 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e131 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b7e43
        have b7e145 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b7e131 X0
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e131
          | exact resolve b7e131 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e131
        have b7e183 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0)) = (M.op (M.op X3 X4) (M.op X0 X0)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e11 X3 (M.op X0 X0) X4
             have i₂ := b7e33 (M.op X0 X0) X1 X2 X0
             grind)
          | exact superpose b7e33 b7e11
          | exact resolve b7e11 b7e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e187 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e11 X0 X4 (M.op X3 X3)
             have i₂ := b7e33 X0 X1 X2 X3
             grind)
          | exact superpose b7e33 b7e11
          | exact resolve b7e11 b7e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e193 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e11 (M.op X0 X2) X1 x
             have i₂ := b7e33 X0 X2 x X1
             grind)
          | exact superpose b7e33 b7e11
          | exact resolve b7e11 b7e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e201 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0)) = (M.op X3 (M.op X0 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e183 X0 X1 X2 X3 x
             have i₂ := b7e193 X3 X0 x
             grind)
          | exact superpose b7e193 b7e183
          | exact resolve b7e183 b7e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e183
        have b7e211 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X0 X0))) := by
          intro X0 X3
          first
          | (have i₁ := b7e201 X0 x x X3
             have i₂ := b7e187 X0 X0 x x X0
             grind)
          | exact superpose b7e187 b7e201
          | exact resolve b7e201 b7e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e201
        have b7e221 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b7e54 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e54
        have b7e222 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e221
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e221
          | exact resolve b7e221 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e221
        have b7e226 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op (σ (k x y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e31 (σ y) (σ x) X0 X1
             have i₂ := b7e222
             grind)
          | exact superpose b7e222 b7e31
          | exact resolve b7e31 b7e222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e227 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ (k x y)) X0) := by
          intro X0
          first
          | (have i₁ := b7e11 (σ y) X0 (σ x)
             have i₂ := b7e222
             grind)
          | exact superpose b7e222 b7e11
          | exact resolve b7e11 b7e222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e296 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 X4) X2) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b7e31 X0 (M.op x x) X2 X4
             have i₂ := b7e34 X0 x X1 X2
             grind)
          | exact superpose b7e34 b7e31
          | exact resolve b7e31 b7e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e34
        have b7e386 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X2) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e36 (M.op X0 X0) X1
             have i₂ := b7e11 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X0 X2
             grind)
          | exact superpose b7e11 b7e36
          | exact resolve b7e36 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e36
        have b7e390 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b7e386 X0 x x
             have i₂ := b7e187 (M.op X0 X0) (M.op X0 X0) x x X0
             grind)
          | exact superpose b7e187 b7e386
          | exact resolve b7e386 b7e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e187 b7e386
        have b7e402 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b7e390 X0
             have i₂ := b7e37 X0 X0 X0
             grind)
          | exact superpose b7e37 b7e390
          | exact resolve b7e390 b7e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e390
        have b7e411 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b7e402 X0
             have i₂ := b7e211 X0 X0
             grind)
          | exact superpose b7e211 b7e402
          | exact resolve b7e402 b7e211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e402
        have b7e432 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e145 X1
             have i₂ := b7e15 (σ X1) X0
             grind)
          | (have i₁ := b7e145 X0
             have i₂ := b7e15 X0 (M.op (σ X0) (σ X0))
             grind)
          | exact superpose b7e15 b7e145
          | (have j1 := b7e15 (σ X1) X0
             grind)
          | exact resolve b7e145 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e526 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) ≠ (M.op (M.op X0 X1) (M.op X2 X2)) ∨ (M.op X2 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e123 (M.op X2 (M.op X2 X2)) X0
             have i₂ := b7e37 X2 X0 X1
             grind)
          | exact superpose b7e37 b7e123
          | (have j0 := b7e123 (M.op X2 (M.op X2 X2)) X0
             grind)
          | (have r₁ := b7e123 (M.op (M.op X2 x) (M.op (M.op X2 x) (M.op X2 x))) X2
             have r₂ := b7e37 (M.op X2 x) X2 x
             grind)
          | exact resolve b7e123 b7e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e123
        have b7e542 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) ≠ (M.op X2 (M.op X2 X2)) ∨ (M.op X2 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X0) := by
          intro X0 X2
          first
          | (have i₁ := b7e526 X0 x X2
             have i₂ := b7e193 X0 X2 x
             grind)
          | exact superpose b7e193 b7e526
          | (have j0 := b7e526 X0 x X2
             grind)
          | (have r₁ := b7e526 x X2 x
             have r₂ := b7e193 x x X2
             grind)
          | (have r₁ := b7e526 X0 x (M.op (M.op X0 x) X2)
             have r₂ := b7e193 (M.op X0 x) (M.op (M.op X0 x) X2) X2
             grind)
          | exact resolve b7e526 b7e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e526
        have b7e1194 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X1)) X4) ∨ (M.op X3 X4) = (k X4 X3) ∨ (M.op X2 X0) = (k X0 X2) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b7e49 X3 X2 X4 X1
             have i₂ := b7e52 X2 X0 X1
             grind)
          | exact superpose b7e52 b7e49
          | (have j0 := b7e49 X3 X1 X4 X3
             have j1 := b7e52 X3 X4 X2
             grind)
          | exact resolve b7e49 b7e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e49 b7e52
        have b7e2940 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e56 X0 X0
             have i₂ := b7e15 (σ X0) X1
             grind)
          | (have i₁ := b7e56 X0 X1
             have i₂ := b7e15 X0 (M.op (σ X0) (σ X1))
             grind)
          | exact superpose b7e15 b7e56
          | (have j1 := b7e15 (σ X1) X0
             grind)
          | exact resolve b7e56 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2956 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e56 x y
             grind)
          | exact superpose b7e56 b7e17
          | (have j1 := b7e56 x y
             grind)
          | exact resolve b7e17 b7e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2959 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e15 (σ X0) X1
             have i₂ := b7e56 X0 X0
             grind)
          | exact superpose b7e56 b7e15
          | (have j0 := b7e15 (σ X0) (σ X0)
             have j1 := b7e56 X0 X0
             grind)
          | exact resolve b7e15 b7e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e2990 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 X1
             have i₂ := b7e56 X1 X0
             grind)
          | exact superpose b7e56 b7e12
          | (have j1 := b7e56 X1 X0
             grind)
          | exact resolve b7e12 b7e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e3034 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b7e56 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e56
        have b7e3328 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ (M.op y x)) X1) ∨ y = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b7e226 X1 X0
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e226
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e226 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e226
        have b7e3516 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ (M.op y x)) X1) := by
          intro X0 X1
          first
          | (have j0 := b7e3328 X0 X1
             grind)
          | (have r₁ := b7e3328 X0 X1
             have r₂ := b7e18
             grind)
          | exact resolve b7e3328 b7e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3328
        have b7e3635 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b7e227 X0
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e227
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e227 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e227
        have b7e3709 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ (M.op y x)) X0) := by
          intro X0
          first
          | (have j0 := b7e3635 X0
             grind)
          | (have r₁ := b7e3635 X0
             have r₂ := b7e18
             grind)
          | exact resolve b7e3635 b7e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3635
        have b7e14345 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e3034 (τ X0)
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e3034
          | (have j0 := b7e3034 (τ X0)
             grind)
          | exact resolve b7e3034 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3034
        have b7e14347 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b7e14345 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e14345
          | (have j0 := b7e14345 X0
             grind)
          | exact resolve b7e14345 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14345
        have b7e14351 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e14347 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e14347
          | (have j0 := b7e14347 X0
             grind)
          | exact resolve b7e14347 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14347
        have b7e14365 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b7e14351 (τ X0)
             have i₂ := b7e60 X0 X0
             grind)
          | exact superpose b7e60 b7e14351
          | (have j0 := b7e14351 (τ X0)
             grind)
          | exact resolve b7e14351 b7e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e14430 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e55 (σ X0) X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e55
          | exact resolve b7e55 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e55
        have b7e14659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e14430 X0 X1
             have i₂ := b7e16 X1 X0
             grind)
          | exact superpose b7e16 b7e14430
          | (have j0 := b7e14430 X0 X1
             grind)
          | exact resolve b7e14430 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14430
        have b7e14901 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e19068 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e15 (σ X0) X1
             have i₂ := b7e116 X0 X0
             grind)
          | exact superpose b7e116 b7e15
          | (have j0 := b7e15 (σ X0) X1
             have j1 := b7e116 X0 X0
             grind)
          | exact resolve b7e15 b7e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e116
        have b7e26262 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e411 X1
             have i₂ := b7e58 X0 X1
             grind)
          | (have i₁ := b7e411 X0
             have i₂ := b7e58 (M.op X0 (M.op X0 X0)) X1
             grind)
          | exact superpose b7e58 b7e411
          | (have j1 := b7e58 X0 X1
             grind)
          | exact resolve b7e411 b7e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e58
        have b7e28510 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b7e2956
             have i₂ := b7e14901 x y
             grind)
          | exact superpose b7e14901 b7e2956
          | (have j1 := b7e14901 x y
             grind)
          | (have r₁ := b7e2956
             have r₂ := b7e14901 x y
             grind)
          | exact resolve b7e2956 b7e14901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14901
        have b7e28511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e2956
             have i₂ := b7e14659 x y
             grind)
          | exact superpose b7e14659 b7e2956
          | (have j1 := b7e14659 (σ x) (σ y)
             grind)
          | (have r₁ := b7e2956
             have r₂ := b7e14659 x y
             grind)
          | exact resolve b7e2956 b7e14659
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2956 b7e14659
        have b7e28512 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
        clear b7e28511
        have b7e28513 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by grind
        clear b7e28510
        have b7e35227 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
          first
          | (have i₁ := b7e145 y
             have i₂ := b7e28513
             grind)
          | exact superpose b7e28513 b7e145
          | exact resolve b7e145 b7e28513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e145 b7e28513
        have b7e35357 : y = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b7e35227
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e35227
          | exact resolve b7e35227 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e35227
        have b7e35358 : y = (k y x) := by grind
        clear b7e35357
        have b7e36899 : (σ x) = (σ (k y y)) ∨ y = (τ (σ x)) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e2990 y y
             have i₂ := b7e28512
             grind)
          | exact superpose b7e28512 b7e2990
          | exact resolve b7e2990 b7e28512
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2990
        have b7e37004 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e36899
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e36899
          | exact resolve b7e36899 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e36899
        have b7e78548 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e432 X0 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e432
          | (have j0 := b7e432 X1 (τ X0)
             grind)
          | exact resolve b7e432 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e78571 : ∀ X0 X1 : G, (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 (τ (σ X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e28 (σ X1) X0
             have i₂ := b7e432 (σ X0) X1
             grind)
          | exact superpose b7e432 b7e28
          | (have j1 := b7e432 (σ X0) X1
             grind)
          | exact resolve b7e28 b7e432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e432
        have b7e78573 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 (τ (σ X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e78571 X0 X1
             have i₂ := b7e12 X1
             grind)
          | exact superpose b7e12 b7e78571
          | (have j0 := b7e78571 X0 X1
             grind)
          | exact resolve b7e78571 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e78571
        have b7e78585 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e78548 X0 X1
             have i₂ := b7e60 X1 X0
             grind)
          | exact superpose b7e60 b7e78548
          | (have j0 := b7e78548 X0 X1
             grind)
          | exact resolve b7e78548 b7e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e60 b7e78548
        have b7e78586 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e78573 X0 X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e78573
          | (have j0 := b7e78573 X0 X1
             grind)
          | exact resolve b7e78573 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e78573
        have b7e95604 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b7e14365 X0
             have i₂ := b7e78585 X0 X0
             grind)
          | exact superpose b7e78585 b7e14365
          | (have j0 := b7e14365 X0
             have j1 := b7e78585 X0 X0
             grind)
          | (have r₁ := b7e14365 x
             have r₂ := b7e78585 x x
             grind)
          | exact resolve b7e14365 b7e78585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14365 b7e78585
        have b7e95606 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b7e95604 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e95604
        have b7e117726 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e12 (k y y)
             have i₂ := b7e37004
             grind)
          | exact superpose b7e37004 b7e12
          | exact resolve b7e12 b7e37004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e37004
        have b7e117736 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e117726
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e117726
          | exact resolve b7e117726 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e117726
        have b7e119427 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e50 y y
             have i₂ := b7e117736
             grind)
          | exact superpose b7e117736 b7e50
          | exact resolve b7e50 b7e117736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e50 b7e117736
        have b7e119435 : x = (M.op y y) ∨ x = y := by grind
        clear b7e119427
        have b7e120902 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op X0 (M.op y x)) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b7e37 y x x
             have i₂ := b7e119435
             grind)
          | exact superpose b7e119435 b7e37
          | exact resolve b7e37 b7e119435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e37
        have b7e120930 : (M.op y x) = (k (M.op y x) (M.op y x)) ∨ x = y := by
          first
          | (have i₁ := b7e411 y
             have i₂ := b7e119435
             grind)
          | exact superpose b7e119435 b7e411
          | exact resolve b7e411 b7e119435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e120965 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e11 y X0 y
             have i₂ := b7e119435
             grind)
          | exact superpose b7e119435 b7e11
          | exact resolve b7e11 b7e119435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e120967 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op x X1) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b7e31 y X0 X1 y
             have i₂ := b7e119435
             grind)
          | exact superpose b7e119435 b7e31
          | exact resolve b7e31 b7e119435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e120975 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op y X2) X1) ∨ x = y := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e79 y y X0 X2 X1
             have i₂ := b7e119435
             grind)
          | exact superpose b7e119435 b7e79
          | exact resolve b7e79 b7e119435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e79
        have b7e121115 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op y x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e120902 X0 x
             have i₂ := b7e11 X0 x x
             grind)
          | exact superpose b7e11 b7e120902
          | exact resolve b7e120902 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e120902
        have b7e128837 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b7e411 y
             have i₂ := b7e120965 y
             grind)
          | exact superpose b7e120965 b7e411
          | exact resolve b7e411 b7e120965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e411
        have b7e129776 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x X1) ∨ x = y ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b7e120967 (M.op X0 X0) X1
             have i₂ := b7e120965 X0
             grind)
          | exact superpose b7e120965 b7e120967
          | exact resolve b7e120967 b7e120965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e120965 b7e120967
        have b7e130144 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x X1) ∨ x = y := by
          intro X0 X1
          first
          | (have j0 := b7e129776 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e129776
        have b7e136904 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e2959 (τ X0) X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e2959
          | (have j0 := b7e2959 (τ X0) X1
             grind)
          | exact resolve b7e2959 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2959
        have b7e137265 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e136904 X0 X1
             have i₂ := b7e23 X0 (τ X0)
             grind)
          | exact superpose b7e23 b7e136904
          | (have j0 := b7e136904 X0 X1
             grind)
          | exact resolve b7e136904 b7e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e23 b7e136904
        have b7e137267 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e137265 X0 X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e137265
          | (have j0 := b7e137265 X0 X1
             grind)
          | exact resolve b7e137265 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e137265
        have b7e140369 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e11 x X0 x
             have i₂ := b7e130144 x X0
             grind)
          | exact superpose b7e130144 b7e11
          | exact resolve b7e11 b7e130144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e130144
        have b7e141911 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b7e140369 y
             have i₂ := b7e119435
             grind)
          | exact superpose b7e119435 b7e140369
          | exact resolve b7e140369 b7e119435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e119435 b7e140369
        have b7e142047 : (M.op x y) = (M.op x x) ∨ x = y := by grind
        clear b7e141911
        have b7e164753 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ x = y := by
          first
          | (have i₁ := b7e14351 (M.op y x)
             have i₂ := b7e120930
             grind)
          | exact superpose b7e120930 b7e14351
          | (have j0 := b7e14351 (M.op y x)
             grind)
          | (have r₁ := b7e14351 (M.op y x)
             have r₂ := b7e120930
             grind)
          | exact resolve b7e14351 b7e120930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e120930
        have b7e164754 : (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ x = y := by grind
        clear b7e164753
        have b7e188400 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e121115 X0
             have i₂ := b7e142047
             grind)
          | exact superpose b7e142047 b7e121115
          | exact resolve b7e121115 b7e142047
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e121115 b7e142047
        have b7e188671 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b7e188400 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e188400
        have b7e196204 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (M.op (M.op X0 (M.op X2 X2)) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b7e1194 X0 X2 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1194
        have b7e196205 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X2 X2)) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b7e196204 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e196204
        have b7e197632 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b7e14351 (M.op x y)
             have i₂ := b7e128837
             grind)
          | exact superpose b7e128837 b7e14351
          | (have j0 := b7e14351 (M.op x y)
             grind)
          | (have r₁ := b7e14351 (M.op x y)
             have r₂ := b7e128837
             grind)
          | exact resolve b7e14351 b7e128837
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e14351 b7e128837
        have b7e197633 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
        clear b7e197632
        have b7e210963 : ∀ X0 : G, (M.op y x) = (M.op (M.op y X0) (M.op y x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e296 y x (M.op y x) x
             have i₂ := b7e164754
             grind)
          | exact superpose b7e164754 b7e296
          | exact resolve b7e296 b7e164754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e296 b7e164754
        have b7e232240 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) (M.op x y)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e120975 y (M.op x y) X0
             have i₂ := b7e197633
             grind)
          | exact superpose b7e197633 b7e120975
          | exact resolve b7e120975 b7e197633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e197633
        have b7e232359 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) (M.op x y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b7e232240 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e232240
        have b7e238988 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) (M.op y x)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e120975 X0 (M.op y x) x
             have i₂ := b7e210963 x
             grind)
          | exact superpose b7e210963 b7e120975
          | exact resolve b7e120975 b7e210963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e120975 b7e210963
        have b7e239118 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) (M.op y x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b7e238988 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e238988
        have b7e267497 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) (M.op y x)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e232359 X0
             have i₂ := b7e188671 (M.op y X0)
             grind)
          | exact superpose b7e188671 b7e232359
          | exact resolve b7e232359 b7e188671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e188671 b7e232359
        have b7e267604 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) (M.op y x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b7e267497 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e267497
        have b7e300930 : (k y y) = (τ (σ x)) ∨ y = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e78586 y y
             have i₂ := b7e28512
             grind)
          | exact superpose b7e28512 b7e78586
          | (have j0 := b7e78586 y y
             grind)
          | exact resolve b7e78586 b7e28512
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e28512 b7e78586
        have b7e300955 : x = (k y y) ∨ y = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e300930
             have i₂ := b7e12 x
             grind)
          | exact superpose b7e12 b7e300930
          | exact resolve b7e300930 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e300930
        have b7e305820 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b7e95606 (σ X0)
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e95606
          | (have j0 := b7e95606 (σ X0)
             grind)
          | exact resolve b7e95606 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e95606
        have b7e305880 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e305820 X0
             have i₂ := b7e16 X0 X0
             grind)
          | exact superpose b7e16 b7e305820
          | (have j0 := b7e305820 X0
             grind)
          | exact resolve b7e305820 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e305820
        have b7e312987 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e300955
             have i₂ := b7e15 y y
             grind)
          | exact superpose b7e15 b7e300955
          | (have j1 := b7e15 y x
             grind)
          | exact resolve b7e300955 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e300955
        have b7e312998 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b7e312987
        have b7e313003 : x = (M.op y y) := by
          first
          | (have r₁ := b7e312998
             have r₂ := b7e20
             grind)
          | exact resolve b7e312998 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e312998
        have b7e315551 : x ≠ y := by
          first
          | (have i₁ := b7e20
             have i₂ := b7e313003
             grind)
          | exact superpose b7e313003 b7e20
          | exact resolve b7e20 b7e313003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e315582 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) x) := by
          intro X0 X1
          first
          | (have i₁ := b7e193 X0 y x
             have i₂ := b7e313003
             grind)
          | exact superpose b7e313003 b7e193
          | exact resolve b7e193 b7e313003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e193
        have b7e315585 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b7e211 y x
             have i₂ := b7e313003
             grind)
          | exact superpose b7e313003 b7e211
          | exact resolve b7e211 b7e313003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e211
        have b7e315661 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b7e11 y X0 y
             have i₂ := b7e313003
             grind)
          | exact superpose b7e313003 b7e11
          | exact resolve b7e11 b7e313003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e315663 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e31 y X0 X1 y
             have i₂ := b7e313003
             grind)
          | exact superpose b7e313003 b7e31
          | exact resolve b7e31 b7e313003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e31
        have b7e315838 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b7e315582 X0 x
             have i₂ := b7e11 X0 x x
             grind)
          | exact superpose b7e11 b7e315582
          | exact resolve b7e315582 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e315582
        have b7e320897 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e239118 X0
             have i₂ := b7e315585 (M.op x X0)
             grind)
          | exact superpose b7e315585 b7e239118
          | exact resolve b7e239118 b7e315585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e239118
        have b7e320899 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b7e267604 X0
             have i₂ := b7e315585 (M.op y X0)
             grind)
          | exact superpose b7e315585 b7e267604
          | exact resolve b7e267604 b7e315585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e267604 b7e315585
        have b7e321101 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) x) := by
          intro X0
          first
          | (have j0 := b7e320899 X0
             grind)
          | (have r₁ := b7e320899 X0
             have r₂ := b7e315551
             grind)
          | exact resolve b7e320899 b7e315551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e320899
        have b7e321103 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) x) := by
          intro X0
          first
          | (have j0 := b7e320897 X0
             grind)
          | (have r₁ := b7e320897 X0
             have r₂ := b7e315551
             grind)
          | exact resolve b7e320897 b7e315551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e320897
        have b7e321265 : (M.op x y) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b7e321101 x
             have i₂ := b7e11 y x x
             grind)
          | exact superpose b7e11 b7e321101
          | exact resolve b7e321101 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e321101
        have b7e321267 : (M.op y x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b7e321103 x
             have i₂ := b7e11 x x x
             grind)
          | exact superpose b7e11 b7e321103
          | exact resolve b7e321103 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e321103
        have b7e321405 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b7e321265
             have i₂ := b7e315838 y
             grind)
          | exact superpose b7e315838 b7e321265
          | exact resolve b7e321265 b7e315838
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e321265
        have b7e321406 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b7e321267
             have i₂ := b7e315838 x
             grind)
          | exact superpose b7e315838 b7e321267
          | exact resolve b7e321267 b7e315838
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e315838 b7e321267
        have b7e321771 : y ≠ (M.op y x) := by
          first
          | (have i₁ := b7e18
             have i₂ := b7e321406
             grind)
          | exact superpose b7e321406 b7e18
          | exact resolve b7e18 b7e321406
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e323108 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op y X1) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b7e33 y X1 X2 X0
             have i₂ := b7e315661 X0
             grind)
          | exact superpose b7e315661 b7e33
          | exact resolve b7e33 b7e315661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e33 b7e315661
        have b7e323318 : ∀ X0 X2 : G, (M.op x X0) = (M.op (M.op x X2) X0) := by
          intro X0 X2
          first
          | (have i₁ := b7e323108 X0 x X2
             have i₂ := b7e315663 x X2
             grind)
          | exact superpose b7e315663 b7e323108
          | exact resolve b7e323108 b7e315663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e315663 b7e323108
        have b7e327581 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e26262 X0 y
             have i₂ := b7e313003
             grind)
          | exact superpose b7e313003 b7e26262
          | (have j0 := b7e26262 X0 x
             grind)
          | exact resolve b7e26262 b7e313003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e26262 b7e313003
        have b7e338555 : y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b7e35358
             have i₂ := b7e137267 y x
             grind)
          | exact superpose b7e137267 b7e35358
          | (have j1 := b7e137267 y x
             grind)
          | exact resolve b7e35358 b7e137267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e35358 b7e137267
        have b7e338565 : y = (M.op x y) ∨ x = (k y y) := by
          first
          | (have r₁ := b7e338555
             have r₂ := b7e20
             grind)
          | exact resolve b7e338555 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e338555
        have b7e338571 : y = (M.op y x) ∨ x = (k y y) := by
          first
          | (have i₁ := b7e338565
             have i₂ := b7e321405
             grind)
          | exact superpose b7e321405 b7e338565
          | exact resolve b7e338565 b7e321405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e338565
        have b7e338579 : x = (k y y) := by
          first
          | (have r₁ := b7e338571
             have r₂ := b7e321771
             grind)
          | exact resolve b7e338571 b7e321771
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e338571
        have b7e341110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e15 X0 X0
             have i₂ := b7e327581 X0
             grind)
          | exact superpose b7e327581 b7e15
          | (have j0 := b7e15 X0 X0
             have j1 := b7e327581 X0
             grind)
          | exact resolve b7e15 b7e327581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e327581
        have b7e341119 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b7e341110 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e341110
        have b7e347821 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e323318 x (M.op x x)
             have i₂ := b7e196205 x X0 x
             grind)
          | exact superpose b7e196205 b7e323318
          | (have j1 := b7e196205 x X0 x
             grind)
          | exact resolve b7e323318 b7e196205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e196205 b7e323318
        have b7e347878 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e347821 X0
             have i₂ := b7e321406
             grind)
          | exact superpose b7e321406 b7e347821
          | (have j0 := b7e347821 X0
             grind)
          | exact resolve b7e347821 b7e321406
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e321406 b7e347821
        have b7e367757 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e321771
             have i₂ := b7e347878 X0
             grind)
          | exact superpose b7e347878 b7e321771
          | (have j1 := b7e347878 X0
             grind)
          | exact resolve b7e321771 b7e347878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e321771 b7e347878
        have b7e367857 : ∀ X0 : G, y ≠ X0 ∨ (k x X0) = (M.op X0 x) ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b7e367757 X0
             have i₂ := b7e341119 X0
             grind)
          | exact superpose b7e341119 b7e367757
          | (have j0 := b7e367757 X0
             have j1 := b7e341119 X0
             grind)
          | (have r₁ := b7e367757 y
             have r₂ := b7e341119 y
             grind)
          | exact resolve b7e367757 b7e341119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e341119 b7e367757
        have b7e367889 : ∀ X0 : G, y ≠ X0 ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b7e367857 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e367857
        have b7e367910 : (k x y) = (M.op y x) := by
          first
          | (have j0 := b7e367889 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e367889
        have b7e370153 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (k y y)) X0) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b7e3516 (σ y) X0
             have i₂ := b7e305880 y
             grind)
          | exact superpose b7e305880 b7e3516
          | (have j1 := b7e305880 y
             grind)
          | exact resolve b7e3516 b7e305880
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3516 b7e305880
        have b7e370170 : ∀ X0 : G, (M.op (σ (M.op y x)) X0) = (M.op (σ (k y y)) X0) := by
          intro X0
          first
          | (have j0 := b7e370153 X0
             grind)
          | (have r₁ := b7e370153 X0
             have r₂ := b7e20
             grind)
          | exact resolve b7e370153 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e370153
        have b7e370175 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y x)) X0) := by
          intro X0
          first
          | (have i₁ := b7e370170 X0
             have i₂ := b7e338579
             grind)
          | exact superpose b7e338579 b7e370170
          | exact resolve b7e370170 b7e338579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e370170
        have b7e370242 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b7e3709 X0
             have i₂ := b7e370175 X0
             grind)
          | exact superpose b7e370175 b7e3709
          | exact resolve b7e3709 b7e370175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e3709 b7e370175
        have b7e395038 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b7e19068 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e19068
        have b7e395039 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b7e395038 X0 X1
             have j1 := b7e2940 X1 X0
             grind)
          | (have r₁ := b7e395038 (k X1 X1) X0
             have r₂ := b7e2940 X0 X1
             grind)
          | (have r₁ := b7e395038 X0 (σ (k X1 X1))
             have r₂ := b7e2940 (σ X0) X1
             grind)
          | (have r₁ := b7e395038 X1 X0
             have r₂ := b7e2940 X0 X1
             grind)
          | exact resolve b7e395038 b7e2940
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2940 b7e395038
        have b7e395124 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b7e22 X1 (τ X1)
             have i₂ := b7e395039 (τ X1) X0
             grind)
          | (have i₁ := b7e22 X0 X1
             have i₂ := b7e395039 X0 (σ (k (τ X0) X1))
             grind)
          | exact superpose b7e395039 b7e22
          | (have j1 := b7e395039 (τ X1) X0
             grind)
          | exact resolve b7e22 b7e395039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e22 b7e395039
        have b7e395131 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b7e395124 X0 X1
             have i₂ := b7e13 X1
             grind)
          | exact superpose b7e13 b7e395124
          | (have j0 := b7e395124 X0 X1
             grind)
          | exact resolve b7e395124 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395124
        have b7e395138 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e395131 X0 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e395131
          | (have j0 := b7e395131 X0 X1
             grind)
          | exact resolve b7e395131 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395131
        have b7e395257 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        clear b7e395138
        have b7e395471 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b7e395257 X0
             have i₂ := b7e11 X0 X0 X0
             grind)
          | exact superpose b7e11 b7e395257
          | (have j0 := b7e395257 X0
             grind)
          | exact resolve b7e395257 b7e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395257
        have b7e395628 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b7e370242 (σ y)
             have i₂ := b7e395471 (σ y)
             grind)
          | exact superpose b7e395471 b7e370242
          | (have j1 := b7e395471 (σ y)
             grind)
          | exact resolve b7e370242 b7e395471
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395471
        have b7e395714 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b7e395628
             have i₂ := b7e16 y y
             grind)
          | exact superpose b7e16 b7e395628
          | exact resolve b7e395628 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395628
        have b7e395739 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e395714
             have i₂ := b7e338579
             grind)
          | exact superpose b7e338579 b7e395714
          | exact resolve b7e395714 b7e338579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395714
        have b7e416639 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have j0 := b7e542 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e542
        have b7e416701 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
          first
          | (have i₁ := b7e416639 (σ y)
             have i₂ := b7e370242 (σ y)
             grind)
          | exact superpose b7e370242 b7e416639
          | exact resolve b7e416639 b7e370242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e416639
        have b7e417123 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
          first
          | (have i₁ := b7e28 (M.op (σ x) (σ y)) y
             have i₂ := b7e416701
             grind)
          | exact superpose b7e416701 b7e28
          | exact resolve b7e28 b7e416701
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e28 b7e416701
        have b7e425212 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e417123
             have i₂ := b7e395739
             grind)
          | exact superpose b7e395739 b7e417123
          | exact resolve b7e417123 b7e395739
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e395739 b7e417123
        have b7e425216 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e425212
             have i₂ := b7e12 y
             grind)
          | exact superpose b7e12 b7e425212
          | exact resolve b7e425212 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e425212
        have b7e425218 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e425216
             have i₂ := b7e338579
             grind)
          | exact superpose b7e338579 b7e425216
          | exact resolve b7e425216 b7e338579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e338579 b7e425216
        have b7e425220 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b7e425218
             have r₂ := b7e315551
             grind)
          | exact resolve b7e425218 b7e315551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e315551 b7e425218
        have b7e425410 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b7e370242 (σ y)
             have i₂ := b7e425220
             grind)
          | exact superpose b7e425220 b7e370242
          | exact resolve b7e370242 b7e425220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e370242 b7e425220
        have b7e425685 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e425410
             have i₂ := b7e222
             grind)
          | exact superpose b7e222 b7e425410
          | exact resolve b7e425410 b7e222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e222 b7e425410
        have b7e425830 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b7e425685
             have i₂ := b7e367910
             grind)
          | exact superpose b7e367910 b7e425685
          | exact resolve b7e425685 b7e367910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e367910 b7e425685
        have b7e426919 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e425830
             grind)
          | exact superpose b7e425830 b7e17
          | exact resolve b7e17 b7e425830
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e425830
        have b7e427067 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e426919
             have i₂ := b7e321405
             grind)
          | exact superpose b7e321405 b7e426919
          | exact resolve b7e426919 b7e321405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e321405 b7e426919
        have b7e427068 : False := by grind
        exact b7e427068

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4478 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op y x) := by grind
        have b0e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e17
          | exact resolve b0e17 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e32 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b0e11 X2 (M.op X0 x) X4 X5
             have i₂ := b0e11 X0 X1 x (M.op X0 x)
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 (σ y) X0 (σ x) X1
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 x X0 y X1
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 y X0 x X1
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X0 X1 x x
             have i₂ := b0e11 X0 X2 x x
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e15 (σ X0) (σ X1)
             grind)
          | exact superpose b0e15 b0e16
          | (have j1 := b0e15 (σ X0) (σ X1)
             grind)
          | exact resolve b0e16 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e52 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e38 x X2
             have i₂ := b0e38 x X0
             grind)
          | (have i₁ := b0e38 X0 x
             have i₂ := b0e38 X0 (M.op X0 X0)
             grind)
          | exact superpose b0e38 b0e38
          | exact resolve b0e38 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e66 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e39 x X2
             have i₂ := b0e39 x X0
             grind)
          | (have i₁ := b0e39 X0 x
             have i₂ := b0e39 X0 (M.op X0 X0)
             grind)
          | exact superpose b0e39 b0e39
          | exact resolve b0e39 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e98 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e20
             have i₂ := b0e52 y X0
             grind)
          | (have i₁ := b0e20
             have i₂ := b0e52 X0 y
             grind)
          | exact superpose b0e52 b0e20
          | exact resolve b0e20 b0e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e52
        have b0e121 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e14 X0 x
             have i₂ := b0e98 X0
             grind)
          | exact superpose b0e98 b0e14
          | (have j0 := b0e14 X0 x
             grind)
          | (have r₁ := b0e14 X0 x
             have r₂ := b0e98 X0
             grind)
          | exact resolve b0e14 b0e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e98
        have b0e125 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b0e121 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e121
        have b0e204 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e37 x X2
             have i₂ := b0e37 x X0
             grind)
          | (have i₁ := b0e37 X0 x
             have i₂ := b0e37 X0 (M.op X0 X0)
             grind)
          | exact superpose b0e37 b0e37
          | exact resolve b0e37 b0e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37
        have b0e243 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e18
             have i₂ := b0e66 x X0
             grind)
          | (have i₁ := b0e18
             have i₂ := b0e66 X0 x
             grind)
          | exact superpose b0e66 b0e18
          | exact resolve b0e18 b0e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e292 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e40 X1 X2 y
             have i₂ := b0e66 y X0
             grind)
          | (have i₁ := b0e40 X1 X2 y
             have i₂ := b0e66 X0 y
             grind)
          | exact superpose b0e66 b0e40
          | exact resolve b0e40 b0e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40 b0e66
        have b0e356 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 y) := by
          intro X1 X2
          first
          | (have i₁ := b0e292 x X1 X2
             have i₂ := b0e243 x
             grind)
          | exact superpose b0e243 b0e292
          | exact resolve b0e292 b0e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e292
        have b0e469 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e32 y x X0 X1 X2
             have i₂ := b0e243 (M.op x x)
             grind)
          | exact superpose b0e243 b0e32
          | exact resolve b0e32 b0e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e243
        have b0e1757 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e47 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e2249 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e19
             have i₂ := b0e204 (σ x) X0
             grind)
          | (have i₁ := b0e19
             have i₂ := b0e204 X0 (σ x)
             grind)
          | exact superpose b0e204 b0e19
          | exact resolve b0e19 b0e204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e204
        have b0e2347 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e32 (σ y) x X0 X1 X2
             have i₂ := b0e2249 (M.op x x)
             grind)
          | exact superpose b0e2249 b0e32
          | exact resolve b0e32 b0e2249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e32 b0e2249
        have b0e2362 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e2347 X0 x x
             have i₂ := b0e469 X0 x x
             grind)
          | exact superpose b0e469 b0e2347
          | exact resolve b0e2347 b0e469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e469 b0e2347
        have b0e2580 : (σ x) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e2362 (σ x)
             grind)
          | exact superpose b0e2362 b0e21
          | exact resolve b0e21 b0e2362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e21 b0e2362
        have b0e6961 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e1757 x
             have i₂ := b0e125 x
             grind)
          | exact superpose b0e125 b0e1757
          | (have j0 := b0e1757 x
             grind)
          | exact resolve b0e1757 b0e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e125 b0e1757
        have b0e6967 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e6961
        have b0e7023 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e356 X0 (σ x)
             have i₂ := b0e6967
             grind)
          | exact superpose b0e6967 b0e356
          | exact resolve b0e356 b0e6967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e356
        have b0e7202 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b0e6967
             have i₂ := b0e7023 (σ x)
             grind)
          | exact superpose b0e7023 b0e6967
          | exact resolve b0e6967 b0e7023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e6967 b0e7023
        have b0e7225 : False := by grind
        exact b0e7225
      · have b1e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op y x) := by grind
        have b1e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e11 X2 (M.op X0 x) X4 X5
             have i₂ := b1e11 X0 X1 x (M.op X0 x)
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e11 X0 x X4 X5
             have i₂ := b1e11 X0 x X1 X2
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 (σ y) X0 (σ x) X1
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 y X0 x X1
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X0 X1 x x
             have i₂ := b1e11 X0 X2 x x
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 X0 X4 X1 (M.op x x)
             have i₂ := b1e11 (M.op X0 X1) x X2 X3
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e35 x X2
             have i₂ := b1e35 x X0
             grind)
          | (have i₁ := b1e35 X0 x
             have i₂ := b1e35 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e35 b1e35
          | exact resolve b1e35 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e77 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e18
             have i₂ := b1e42 x X0
             grind)
          | (have i₁ := b1e18
             have i₂ := b1e42 X0 x
             grind)
          | exact superpose b1e42 b1e18
          | exact resolve b1e18 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e88 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k (τ X0) X1)
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k X0 (τ X1))
             have i₂ := b1e27 X1 X0
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e173 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e34 x X2
             have i₂ := b1e34 x X0
             grind)
          | (have i₁ := b1e34 X0 x
             have i₂ := b1e34 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e34 b1e34
          | exact resolve b1e34 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e223 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 X0 X1 y
             have i₂ := b1e77 y
             grind)
          | exact superpose b1e77 b1e36
          | exact resolve b1e36 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e350 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 y x X0 X1 X2
             have i₂ := b1e77 (M.op x x)
             grind)
          | exact superpose b1e77 b1e29
          | exact resolve b1e29 b1e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e672 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e14 X4 (M.op (M.op X0 X2) X3)
             have i₂ := b1e37 X0 X2 X3 X4 X1
             grind)
          | exact superpose b1e37 b1e14
          | (have j0 := b1e14 X4 (M.op (M.op X0 X2) X3)
             grind)
          | exact resolve b1e14 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e689 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X2 X3 X4
          first
          | (have j0 := b1e672 X0 x X2 X3 X4
             grind)
          | (have r₁ := b1e672 X0 x X2 X3 X4
             have r₂ := b1e11 X0 x X2 X3
             grind)
          | exact resolve b1e672 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e672
        have b1e748 : ∀ X0 X4 : G, (k X4 (M.op X0 y)) = X4 := by
          intro X0 X4
          first
          | (have i₁ := b1e689 X0 x x X4
             have i₂ := b1e350 X0 x x
             grind)
          | exact superpose b1e350 b1e689
          | exact resolve b1e689 b1e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e689
        have b1e1320 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e19
             have i₂ := b1e173 (σ x) X0
             grind)
          | (have i₁ := b1e19
             have i₂ := b1e173 X0 (σ x)
             grind)
          | exact superpose b1e173 b1e19
          | exact resolve b1e19 b1e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e173
        have b1e1462 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 (σ y) x X0 X1 X2
             have i₂ := b1e1320 (M.op x x)
             grind)
          | exact superpose b1e1320 b1e29
          | exact resolve b1e29 b1e1320
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e1320
        have b1e1474 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1462 X0 x x
             have i₂ := b1e350 X0 x x
             grind)
          | exact superpose b1e350 b1e1462
          | exact resolve b1e1462 b1e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1462
        have b1e1674 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e57 X1 X0
             have i₂ := b1e57 X0 X1
             grind)
          | exact superpose b1e57 b1e57
          | (have j0 := b1e57 X1 X0
             have j1 := b1e57 X1 X0
             grind)
          | exact resolve b1e57 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1708 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (σ X1) (σ X0)
             have i₂ := b1e57 X1 X0
             grind)
          | exact superpose b1e57 b1e14
          | (have j0 := b1e14 (σ X1) (σ X0)
             have j1 := b1e57 X1 X0
             grind)
          | (have r₁ := b1e14 (σ X0) (σ X1)
             have r₂ := b1e57 X0 X1
             grind)
          | exact resolve b1e14 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1712 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X0) X4) = (M.op (M.op (σ X0) X1) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e30 (σ X0) X1 X2 (σ X3) X4
             have i₂ := b1e57 X3 X0
             grind)
          | exact superpose b1e57 b1e30
          | (have j1 := b1e57 X3 X0
             grind)
          | exact resolve b1e30 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e1717 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e57 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1718 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e1708 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1708
        have b1e1720 : ∀ X0 X3 X4 : G, (M.op (σ X0) X4) = (M.op (σ X0) y) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
          intro X0 X3 X4
          first
          | (have i₁ := b1e1712 X0 x x X3 X4
             have i₂ := b1e350 (σ X0) x x
             grind)
          | exact superpose b1e350 b1e1712
          | (have j0 := b1e1712 X0 x x X3 X4
             grind)
          | exact resolve b1e1712 b1e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1712
        have b1e1724 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1718 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e1718
          | (have j0 := b1e1718 X0 X1
             grind)
          | exact resolve b1e1718 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1718
        have b1e1812 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e1474 (σ x)
             grind)
          | exact superpose b1e1474 b1e17
          | exact resolve b1e17 b1e1474
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1474
        have b1e2054 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e88 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e88
          | exact resolve b1e88 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2203 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e111 X0 (M.op X1 y)
             have i₂ := b1e748 X1 (σ X0)
             grind)
          | exact superpose b1e748 b1e111
          | exact resolve b1e111 b1e748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e748
        have b1e2223 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 y))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e2203 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e2203
          | exact resolve b1e2203 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2203
        have b1e2567 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e111 X0 (τ (M.op X1 y))
             have i₂ := b1e2223 (σ X0) X1
             grind)
          | exact superpose b1e2223 b1e111
          | exact resolve b1e111 b1e2223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e111 b1e2223
        have b1e2570 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 y)))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e2567 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e2567
          | exact resolve b1e2567 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2567
        have b1e5386 : ∀ X0 : G, (σ (τ (τ (M.op X0 y)))) ≠ (σ (τ (τ (M.op X0 y)))) ∨ (σ (τ (τ (M.op X0 y)))) = (M.op (σ (τ (τ (M.op X0 y)))) (σ (τ (τ (M.op X0 y))))) := by
          intro X0
          first
          | (have i₁ := b1e1717 (τ (τ (M.op X0 y)))
             have i₂ := b1e2570 (τ (τ (M.op X0 y))) X0
             grind)
          | exact superpose b1e2570 b1e1717
          | (have j0 := b1e1717 (τ (τ (M.op X0 y)))
             grind)
          | exact resolve b1e1717 b1e2570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2570
        have b1e5395 : ∀ X0 : G, (σ (τ (τ (M.op X0 y)))) = (M.op (σ (τ (τ (M.op X0 y)))) (σ (τ (τ (M.op X0 y))))) := by
          intro X0
          first
          | (have j0 := b1e5386 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5386
        have b1e5418 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e5395 X0
             have i₂ := b1e13 (τ (M.op X0 y))
             grind)
          | exact superpose b1e13 b1e5395
          | exact resolve b1e5395 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5395
        have b1e6430 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e1724 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e1724
          | exact resolve b1e1724 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1724
        have b1e6526 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e6430 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e6430
          | (have j0 := b1e6430 X0 X1
             grind)
          | exact resolve b1e6430 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6430
        have b1e6536 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e6526 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e6526
          | (have j0 := b1e6526 X0 X1
             grind)
          | exact resolve b1e6526 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6526
        have b1e6816 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1720 (τ X0) x x
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e1720
          | exact resolve b1e1720 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6845 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e57 X2 X0
             have i₂ := b1e1720 X0 X1 (σ X2)
             grind)
          | exact superpose b1e1720 b1e57
          | (have j0 := b1e57 X2 X0
             have j1 := b1e1720 X0 X2 x
             grind)
          | exact resolve b1e57 b1e1720
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e1720
        have b1e7027 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e6816 X0 X1 X2
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e6816
          | (have j0 := b1e6816 X0 X1 X2
             grind)
          | exact resolve b1e6816 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6816
        have b1e8505 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e1674 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e1674
          | exact resolve b1e1674 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e8554 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (σ X1) (σ X0)
             have i₂ := b1e1674 X1 X0
             grind)
          | exact superpose b1e1674 b1e14
          | (have j0 := b1e14 (σ X1) (σ X0)
             have j1 := b1e1674 X1 X0
             grind)
          | (have r₁ := b1e14 (σ X0) (σ X1)
             have r₂ := b1e1674 X0 X1
             grind)
          | exact resolve b1e14 b1e1674
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1674
        have b1e8589 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e8554 X0 X1
             have j1 := b1e14 (σ X1) (σ X0)
             grind)
          | (have r₁ := b1e8554 X0 X1
             have r₂ := b1e14 (σ X1) (σ X0)
             grind)
          | exact resolve b1e8554 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8554
        have b1e8599 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e8505 X0 X1
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e8505
          | (have j0 := b1e8505 X0 X1
             grind)
          | exact resolve b1e8505 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8505
        have b1e8610 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e8589 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e8589
          | (have j0 := b1e8589 X0 X1
             grind)
          | exact resolve b1e8589 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8589
        have b1e8611 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e8610 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8610
        have b1e8619 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e8599 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e8599
          | (have j0 := b1e8599 X0 X1
             grind)
          | exact resolve b1e8599 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8599
        have b1e8627 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b1e8619 X0 X1
             have j1 := b1e14 X0 (σ X1)
             grind)
          | (have r₁ := b1e8619 X0 X1
             have r₂ := b1e14 X0 (σ X1)
             grind)
          | exact resolve b1e8619 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8619
        have b1e11004 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e8611 (τ X0) (τ X1)
             have i₂ := b1e2054 X1 X0
             grind)
          | exact superpose b1e2054 b1e8611
          | (have j0 := b1e8611 (τ X0) (τ X1)
             grind)
          | exact resolve b1e8611 b1e2054
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2054
        have b1e11063 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e11004 X0 X1
             have i₂ := b1e13 (k X0 X1)
             grind)
          | exact superpose b1e13 b1e11004
          | (have j0 := b1e11004 X0 X1
             grind)
          | exact resolve b1e11004 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11004
        have b1e11082 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e11063 X0 X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e11063
          | (have j0 := b1e11063 X0 X1
             grind)
          | exact resolve b1e11063 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11063
        have b1e11093 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e11082 X0 X1
             have i₂ := b1e27 X0 (τ X1)
             grind)
          | exact superpose b1e27 b1e11082
          | (have j0 := b1e11082 X0 X1
             grind)
          | exact resolve b1e11082 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11082
        have b1e11095 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e11093 X0 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e11093
          | (have j0 := b1e11093 X0 X1
             grind)
          | exact resolve b1e11093 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11093
        have b1e12240 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e6536 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e6536
          | exact resolve b1e6536 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6536
        have b1e12491 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e8627 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e8627
          | exact resolve b1e8627 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8627
        have b1e13973 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X2) = (M.op X1 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e7027 X0 (τ X0) X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e7027
          | (have j0 := b1e7027 X1 X1 X2
             grind)
          | exact resolve b1e7027 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7027
        have b1e19709 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e12240 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12240
        have b1e20538 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e8611 X0 X1
             have i₂ := b1e12491 X1 X0
             grind)
          | exact superpose b1e12491 b1e8611
          | (have j0 := b1e8611 X0 X1
             have j1 := b1e12491 X1 X0
             grind)
          | exact resolve b1e8611 b1e12491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8611 b1e12491
        have b1e20585 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e20538 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e20538
        have b1e42416 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X2) = (M.op X1 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e26 X0 X1
             have i₂ := b1e13973 (τ X0) X1 X2
             grind)
          | exact superpose b1e13973 b1e26
          | (have j1 := b1e13973 X0 X1 X2
             grind)
          | exact resolve b1e26 b1e13973
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42795 : ∀ X0 X1 : G, x ≠ (M.op x X0) ∨ (k X1 x) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e20
             have i₂ := b1e13973 X1 x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e13973 X0 x y
             grind)
          | exact superpose b1e13973 b1e20
          | (have j1 := b1e13973 X1 x x
             grind)
          | exact resolve b1e20 b1e13973
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13973
        have b1e52241 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e223 X1 (τ (M.op X0 y))
             have i₂ := b1e5418 X0
             grind)
          | exact superpose b1e5418 b1e223
          | exact resolve b1e223 b1e5418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52831 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e5418 X0
             have i₂ := b1e52241 X0 (τ (M.op X0 y))
             grind)
          | exact superpose b1e52241 b1e5418
          | exact resolve b1e5418 b1e52241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5418 b1e52241
        have b1e54366 : ∀ X0 X1 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e350 (τ (M.op X0 y)) y x
             have i₂ := b1e52831 X0
             grind)
          | exact superpose b1e52831 b1e350
          | exact resolve b1e350 b1e52831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52831
        have b1e55578 : ∀ X0 X1 : G, (τ (τ (M.op X0 y))) = (M.op (τ (τ (M.op X0 y))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e54366 (τ (M.op X0 y)) X1
             have i₂ := b1e54366 X0 y
             grind)
          | exact superpose b1e54366 b1e54366
          | exact resolve b1e54366 b1e54366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66022 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e1717 X0
             have i₂ := b1e20585 X0 X0
             grind)
          | exact superpose b1e20585 b1e1717
          | (have j0 := b1e1717 X0
             have j1 := b1e20585 X0 X0
             grind)
          | (have r₁ := b1e1717 X0
             have r₂ := b1e20585 X0 X0
             grind)
          | exact resolve b1e1717 b1e20585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1717 b1e20585
        have b1e66179 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e66022 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66022
        have b1e81915 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) y) := by
          intro X0 X1
          first
          | (have j0 := b1e6845 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6845
        have b1e81916 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) y) := by
          intro X0 X1
          first
          | (have j0 := b1e81915 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81915
        have b1e115397 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e223 X1 (σ X0)
             have i₂ := b1e66179 X0
             grind)
          | exact superpose b1e66179 b1e223
          | (have j1 := b1e66179 X0
             grind)
          | exact resolve b1e223 b1e66179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e223
        have b1e122315 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e66179 X0
             have i₂ := b1e115397 X0 (σ X0)
             grind)
          | exact superpose b1e115397 b1e66179
          | (have j0 := b1e66179 X0
             have j1 := b1e115397 X0 x
             grind)
          | exact resolve b1e66179 b1e115397
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66179 b1e115397
        have b1e122485 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e122315 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122315
        have b1e123052 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e54366 (σ X0) X1
             have i₂ := b1e122485 X0
             grind)
          | exact superpose b1e122485 b1e54366
          | (have j1 := b1e122485 X0
             grind)
          | exact resolve b1e54366 b1e122485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54366
        have b1e123054 : ∀ X0 X1 : G, (τ (τ (σ X0))) = (M.op (τ (τ (σ X0))) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e55578 (σ X0) X1
             have i₂ := b1e122485 X0
             grind)
          | exact superpose b1e122485 b1e55578
          | (have j1 := b1e122485 X0
             grind)
          | exact resolve b1e55578 b1e122485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55578 b1e122485
        have b1e123224 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e123054 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e123054
          | (have j0 := b1e123054 X0 X1
             grind)
          | exact resolve b1e123054 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123054
        have b1e123226 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e123052 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e123052
          | (have j0 := b1e123052 X0 X1
             grind)
          | exact resolve b1e123052 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123052
        have b1e124309 : ∀ X1 : G, x ≠ x ∨ (k X1 x) = (M.op X1 x) ∨ (k x x) = (M.op x x) := by
          intro X1
          first
          | (have i₁ := b1e42795 x X1
             have i₂ := b1e123226 x x
             grind)
          | exact superpose b1e123226 b1e42795
          | (have j0 := b1e42795 x X1
             have j1 := b1e123226 x X1
             grind)
          | (have r₁ := b1e42795 X1 X1
             have r₂ := b1e123226 x X1
             grind)
          | exact resolve b1e42795 b1e123226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123226
        have b1e124443 : ∀ X1 : G, (k X1 x) = (M.op X1 x) ∨ (k x x) = (M.op x x) := by
          intro X1
          first
          | (have j0 := b1e124309 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124309
        have b1e132290 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e123224 (σ X0) X1
             grind)
          | exact superpose b1e123224 b1e16
          | (have j1 := b1e123224 (σ X0) X1
             grind)
          | exact resolve b1e16 b1e123224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123224
        have b1e132339 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e132290 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e132290
          | (have j0 := b1e132290 X0 X1
             grind)
          | exact resolve b1e132290 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e132290
        have b1e132928 : (M.op x x) ≠ (M.op x x) ∨ (k x x) = (M.op x x) := by
          first
          | (have j0 := b1e124443 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124443
        have b1e132929 : (k x x) = (M.op x x) := by grind
        clear b1e132928
        have b1e170897 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op X0 y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e350 X0 x X2
             have i₂ := b1e132339 X0 x
             grind)
          | exact superpose b1e132339 b1e350
          | (have j1 := b1e132339 X0 x
             grind)
          | exact resolve b1e350 b1e132339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e230630 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e81916 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e81916
          | exact resolve b1e81916 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81916
        have b1e230755 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e230630 X0 X1
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e230630
          | (have j0 := b1e230630 X0 X1
             grind)
          | exact resolve b1e230630 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e230630
        have b1e230773 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e230755 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e230755
          | (have j0 := b1e230755 X1 X1
             grind)
          | exact resolve b1e230755 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e230755
        have b1e231279 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e26 X0 X1
             have i₂ := b1e230773 (τ X0) X1
             grind)
          | exact superpose b1e230773 b1e26
          | (have j1 := b1e230773 X0 X1
             grind)
          | exact resolve b1e26 b1e230773
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e230773
        have b1e232216 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e231279 (σ X0) X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e231279
          | (have j0 := b1e231279 X0 X1
             grind)
          | exact resolve b1e231279 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e231279
        have b1e232328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e232216 X0 X1
             have i₂ := b1e16 X0 X1
             grind)
          | exact superpose b1e16 b1e232216
          | (have j0 := b1e232216 X0 X1
             grind)
          | exact resolve b1e232216 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e232216
        have b1e303837 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op X1 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e42416 (σ X0) X1 X2
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e42416
          | (have j0 := b1e42416 X0 X1 X2
             grind)
          | exact resolve b1e42416 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42416
        have b1e303942 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op X1 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e303837 X0 X1 X2
             have i₂ := b1e16 X0 X1
             grind)
          | exact superpose b1e16 b1e303837
          | (have j0 := b1e303837 X0 X1 X2
             grind)
          | exact resolve b1e303837 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e303837
        have b1e304068 : ∀ X0 X1 X2 : G, (M.op X0 y) ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e19709 X0 X1
             have i₂ := b1e303942 X2 X0 X1
             grind)
          | (have i₁ := b1e19709 X1 y
             have i₂ := b1e303942 X0 X1 X2
             grind)
          | exact superpose b1e303942 b1e19709
          | (have j0 := b1e19709 X0 y
             have j1 := b1e303942 X2 X0 X2
             grind)
          | exact resolve b1e19709 b1e303942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19709 b1e303942
        have b1e304135 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e304068 X0 X1 X2
             have j1 := b1e232328 X2 X0
             grind)
          | (have r₁ := b1e304068 X1 X1 X2
             have r₂ := b1e232328 X0 X1
             grind)
          | exact resolve b1e304068 b1e232328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e232328 b1e304068
        have b1e304365 : ∀ X0 X1 X2 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (k X0 X1)
             have i₂ := b1e304135 X1 X2 X0
             grind)
          | exact superpose b1e304135 b1e12
          | (have j1 := b1e304135 X1 X2 X2
             grind)
          | exact resolve b1e12 b1e304135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304135
        have b1e304382 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e304365 X0 X1 X2
             have i₂ := b1e12 (M.op X0 X1)
             grind)
          | exact superpose b1e12 b1e304365
          | (have j0 := b1e304365 X0 X1 X2
             grind)
          | exact resolve b1e304365 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304365
        have b1e304713 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e88 X0 X1
             have i₂ := b1e304382 X2 X0 (σ X1)
             grind)
          | exact superpose b1e304382 b1e88
          | (have j1 := b1e304382 X2 X0 X2
             grind)
          | exact resolve b1e88 b1e304382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e304742 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e132929
             have i₂ := b1e304382 X0 x x
             grind)
          | exact superpose b1e304382 b1e132929
          | (have j1 := b1e304382 X0 x x
             grind)
          | exact resolve b1e132929 b1e304382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304382
        have b1e304752 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b1e304742 X0
             have j1 := b1e42795 X0 X0
             grind)
          | (have r₁ := b1e304742 X0
             have r₂ := b1e42795 x x
             grind)
          | exact resolve b1e304742 b1e42795
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42795 b1e304742
        have b1e307451 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e88 X0 X1
             have i₂ := b1e304713 (σ X1) X2 X0
             grind)
          | exact superpose b1e304713 b1e88
          | (have j1 := b1e304713 (σ X1) X2 X2
             grind)
          | exact resolve b1e88 b1e304713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88 b1e304713
        have b1e307481 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e307451 X0 X0 X2
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e307451
          | (have j0 := b1e307451 X0 X1 X2
             grind)
          | exact resolve b1e307451 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e307451
        have b1e313559 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 y)) = (k (τ (M.op X0 X1)) X2) ∨ (k X2 X3) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e307481 (M.op X0 X1) X2 X3
             have i₂ := b1e350 X0 X1 (σ X2)
             grind)
          | exact superpose b1e350 b1e307481
          | (have j0 := b1e307481 X0 X2 X3
             grind)
          | exact resolve b1e307481 b1e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e307481
        have b1e325767 : ∀ X0 X1 X2 X3 : G, (σ (τ (M.op X0 y))) = (k (M.op X0 X1) (σ X2)) ∨ (k X2 X3) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e26 (M.op X0 X1) X2
             have i₂ := b1e313559 X0 X1 X2 X3
             grind)
          | exact superpose b1e313559 b1e26
          | (have j1 := b1e313559 X0 X1 X2 X3
             grind)
          | exact resolve b1e26 b1e313559
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e313559
        have b1e325784 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (k (M.op X0 X1) (σ X2)) ∨ (k X2 X3) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e325767 X0 X1 X2 X3
             have i₂ := b1e13 (M.op X0 y)
             grind)
          | exact superpose b1e13 b1e325767
          | (have j0 := b1e325767 X0 X1 X2 X3
             grind)
          | exact resolve b1e325767 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e325767
        have b1e325958 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 y) = (k (M.op X2 X3) (σ X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11095 X0 X1
             have i₂ := b1e325784 X2 X3 X0 X1
             grind)
          | exact superpose b1e325784 b1e11095
          | (have j0 := b1e11095 X0 X1
             have j1 := b1e325784 X2 X3 X0 X3
             grind)
          | (have r₁ := b1e11095 (M.op X0 y) (σ X2)
             have r₂ := b1e325784 X0 y X2 X3
             grind)
          | (have r₁ := b1e11095 X2 X3
             have r₂ := b1e325784 X0 X1 X2 X3
             grind)
          | exact resolve b1e11095 b1e325784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11095 b1e325784
        have b1e325967 : ∀ X0 X1 X2 X3 : G, (k X1 X0) = X1 ∨ (M.op X2 y) = (k (M.op X2 X3) (σ X0)) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b1e325958 X0 X1 X2 X3
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e325958
        have b1e326143 : ∀ X0 X1 X2 : G, (M.op X0 x) = X0 ∨ (M.op X1 y) = (k (M.op X1 X2) (σ x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e304752 X0
             have i₂ := b1e325967 x X0 X1 X2
             grind)
          | exact superpose b1e325967 b1e304752
          | (have j1 := b1e325967 x X1 X1 X2
             grind)
          | exact resolve b1e304752 b1e325967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e325967
        have b1e378696 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e170897 x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e170897 x y
             grind)
          | exact superpose b1e170897 b1e20
          | (have j1 := b1e170897 x x
             grind)
          | exact resolve b1e20 b1e170897
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e170897
        have b1e378709 : (σ (k x x)) = (M.op (σ x) (σ x)) := by
          first
          | (have j1 := b1e132339 x x
             grind)
          | (have r₁ := b1e378696 x
             have r₂ := b1e132339 x x
             grind)
          | exact resolve b1e378696 b1e132339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e132339 b1e378696
        have b1e378710 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e378709
             have i₂ := b1e132929
             grind)
          | exact superpose b1e132929 b1e378709
          | exact resolve b1e378709 b1e132929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e132929 b1e378709
        have b1e378937 : ∀ X0 : G, (M.op (σ x) y) = (k (σ (M.op x x)) (σ x)) ∨ (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e326143 X0 (σ x) (σ x)
             have i₂ := b1e378710
             grind)
          | exact superpose b1e378710 b1e326143
          | (have j0 := b1e326143 X0 x x
             grind)
          | exact resolve b1e326143 b1e378710
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e326143 b1e378710
        have b1e378953 : ∀ X0 : G, (M.op (σ x) y) = (σ (k (M.op x x) x)) ∨ (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e378937 X0
             have i₂ := b1e16 (M.op x x) x
             grind)
          | exact superpose b1e16 b1e378937
          | (have j0 := b1e378937 X0
             grind)
          | exact resolve b1e378937 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e378937
        have b1e379034 : ∀ X0 : G, (M.op (σ x) y) = (σ (M.op (M.op x x) x)) ∨ (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e378953 X0
             have i₂ := b1e304752 (M.op x x)
             grind)
          | exact superpose b1e304752 b1e378953
          | (have j0 := b1e378953 X0
             grind)
          | exact resolve b1e378953 b1e304752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304752 b1e378953
        have b1e379059 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) y) ∨ (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e379034 X0
             have i₂ := b1e350 x x x
             grind)
          | exact superpose b1e350 b1e379034
          | (have j0 := b1e379034 X0
             grind)
          | exact resolve b1e379034 b1e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e379034
        have b1e379064 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b1e379059 X0
             grind)
          | (have r₁ := b1e379059 X0
             have r₂ := b1e1812
             grind)
          | exact resolve b1e379059 b1e1812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1812 b1e379059
        have b1e379267 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 X0 X1 x
             have i₂ := b1e379064 x
             grind)
          | exact superpose b1e379064 b1e36
          | exact resolve b1e36 b1e379064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e379561 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e350 X0 X1 x
             have i₂ := b1e379064 (M.op X0 X1)
             grind)
          | exact superpose b1e379064 b1e350
          | exact resolve b1e350 b1e379064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e350
        have b1e380144 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e379267 X0 X1
             have i₂ := b1e379064 X0
             grind)
          | exact superpose b1e379064 b1e379267
          | exact resolve b1e379267 b1e379064
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e379064 b1e379267
        have b1e380198 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e380144 X0 x
             have i₂ := b1e379561 X0 (M.op x x)
             grind)
          | exact superpose b1e379561 b1e380144
          | exact resolve b1e380144 b1e379561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e379561 b1e380144
        have b1e382410 : x ≠ x := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e380198 x
             grind)
          | exact superpose b1e380198 b1e20
          | (have r₁ := b1e20
             have r₂ := b1e380198 x
             grind)
          | exact resolve b1e20 b1e380198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e380198
        have b1e382459 : False := by grind
        exact b1e382459
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b2e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e17
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17
          | exact resolve b2e17 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e23 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b2e14 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e14
          | (have j0 := b2e14 y x
             grind)
          | (have r₁ := b2e14 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e14 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : y = (k y x) := by grind
        clear b2e23
        have b2e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact superpose b2e15 b2e16
          | (have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e16 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1647 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e43 y x
             grind)
          | exact superpose b2e43 b2e21
          | (have j1 := b2e43 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e43 y x
             grind)
          | exact resolve b2e21 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21 b2e43
        have b2e1660 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
        clear b2e1647
        have b2e1668 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e1660
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1660
          | exact resolve b2e1660 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1660
        have b2e1692 : False := by grind
        exact b2e1692
      · have b3e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op y x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e26 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b3e11 X2 (M.op X0 x) X4 X5
             have i₂ := b3e11 X0 X1 x (M.op X0 x)
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e11 y X0 x X1
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 X0 X1 x x
             have i₂ := b3e11 X0 X2 x x
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b3e29 x X2
             have i₂ := b3e29 x X0
             grind)
          | (have i₁ := b3e29 X0 x
             have i₂ := b3e29 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e29 b3e29
          | exact resolve b3e29 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e15 (σ X0) (σ X1)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X0) (σ X1)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e18
             have i₂ := b3e38 x X0
             grind)
          | (have i₁ := b3e18
             have i₂ := b3e38 X0 x
             grind)
          | exact superpose b3e38 b3e18
          | exact resolve b3e18 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e95 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e14 X0 y
             have i₂ := b3e73 X0
             grind)
          | exact superpose b3e73 b3e14
          | (have j0 := b3e14 X0 y
             grind)
          | (have r₁ := b3e14 X0 y
             have r₂ := b3e73 X0
             grind)
          | exact resolve b3e14 b3e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e98 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e95 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95
        have b3e180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X0 X1 y
             have i₂ := b3e73 y
             grind)
          | exact superpose b3e73 b3e32
          | exact resolve b3e32 b3e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e274 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e26 y x X0 X1 X2
             have i₂ := b3e73 (M.op x x)
             grind)
          | exact superpose b3e73 b3e26
          | exact resolve b3e26 b3e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e73
        have b3e1649 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e53 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e5002 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1649 y
             have i₂ := b3e98 y
             grind)
          | exact superpose b3e98 b3e1649
          | (have j0 := b3e1649 y
             grind)
          | exact resolve b3e1649 b3e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98 b3e1649
        have b3e5007 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e5002
        have b3e5051 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e180 X0 (σ y)
             have i₂ := b3e5007
             grind)
          | exact superpose b3e5007 b3e180
          | exact resolve b3e180 b3e5007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e180
        have b3e5226 : (σ y) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e5007
             have i₂ := b3e5051 (σ y)
             grind)
          | exact superpose b3e5051 b3e5007
          | exact resolve b3e5007 b3e5051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5007 b3e5051
        have b3e5516 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e274 (σ y) y x
             have i₂ := b3e5226
             grind)
          | exact superpose b3e5226 b3e274
          | exact resolve b3e274 b3e5226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e274 b3e5226
        have b3e5696 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e5516 (σ x)
             grind)
          | exact superpose b3e5516 b3e19
          | (have r₁ := b3e19
             have r₂ := b3e5516 (σ x)
             grind)
          | exact resolve b3e19 b3e5516
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5516
        have b3e5765 : False := by grind
        exact b3e5765
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op y x) := by grind
        have b4e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b4e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X1 (τ X0)
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e16
          | exact resolve b4e16 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e30 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b4e11 X2 (M.op X0 x) X4 X5
             have i₂ := b4e11 X0 X1 x (M.op X0 x)
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e35 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 (σ y) X0 (σ x) X1
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e11
          | exact resolve b4e11 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e36 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 x X0 y X1
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e11 X0 X1 x x
             have i₂ := b4e11 X0 X2 x x
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b4e11 X0 X4 X1 (M.op x x)
             have i₂ := b4e11 (M.op X0 X1) x X2 X3
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X0 X1
             have i₂ := b4e15 (σ X0) (σ X1)
             grind)
          | exact superpose b4e15 b4e16
          | (have j1 := b4e15 (σ X0) (σ X1)
             grind)
          | exact resolve b4e16 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e57 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b4e36 x X2
             have i₂ := b4e36 x X0
             grind)
          | (have i₁ := b4e36 X0 x
             have i₂ := b4e36 X0 (M.op X0 X0)
             grind)
          | exact superpose b4e36 b4e36
          | exact resolve b4e36 b4e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e36
        have b4e88 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b4e20
             have i₂ := b4e57 y X0
             grind)
          | (have i₁ := b4e20
             have i₂ := b4e57 X0 y
             grind)
          | exact superpose b4e57 b4e20
          | exact resolve b4e20 b4e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e57
        have b4e122 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e12 (k X0 (τ X1))
             have i₂ := b4e28 X1 X0
             grind)
          | exact superpose b4e28 b4e12
          | exact resolve b4e12 b4e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e28
        have b4e184 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
          intro X0 X2
          first
          | (have i₁ := b4e35 x X2
             have i₂ := b4e35 x X0
             grind)
          | (have i₁ := b4e35 X0 x
             have i₂ := b4e35 X0 (M.op X0 X0)
             grind)
          | exact superpose b4e35 b4e35
          | exact resolve b4e35 b4e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e35
        have b4e234 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b4e37 X0 X1 x
             have i₂ := b4e88 x
             grind)
          | exact superpose b4e88 b4e37
          | exact resolve b4e37 b4e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e37
        have b4e361 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e30 x x X0 X1 X2
             have i₂ := b4e88 (M.op x x)
             grind)
          | exact superpose b4e88 b4e30
          | exact resolve b4e30 b4e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e30 b4e88
        have b4e683 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b4e14 X4 (M.op (M.op X0 X2) X3)
             have i₂ := b4e38 X0 X2 X3 X4 X1
             grind)
          | exact superpose b4e38 b4e14
          | (have j0 := b4e14 X4 (M.op (M.op X0 X2) X3)
             grind)
          | exact resolve b4e14 b4e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e38
        have b4e700 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X2 X3 X4
          first
          | (have j0 := b4e683 X0 x X2 X3 X4
             grind)
          | (have r₁ := b4e683 X0 x X2 X3 X4
             have r₂ := b4e11 X0 x X2 X3
             grind)
          | exact resolve b4e683 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e683
        have b4e759 : ∀ X0 X4 : G, (k X4 (M.op X0 x)) = X4 := by
          intro X0 X4
          first
          | (have i₁ := b4e700 X0 x x X4
             have i₂ := b4e361 X0 x x
             grind)
          | exact superpose b4e361 b4e700
          | exact resolve b4e700 b4e361
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e361 b4e700
        have b4e1331 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b4e19
             have i₂ := b4e184 (σ x) X0
             grind)
          | (have i₁ := b4e19
             have i₂ := b4e184 X0 (σ x)
             grind)
          | exact superpose b4e184 b4e19
          | exact resolve b4e19 b4e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e184
        have b4e1480 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b4e759 (σ y) X0
             have i₂ := b4e1331 x
             grind)
          | exact superpose b4e1331 b4e759
          | exact resolve b4e759 b4e1331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e759 b4e1331
        have b4e1648 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b4e16 X0 y
             have i₂ := b4e1480 (σ X0)
             grind)
          | exact superpose b4e1480 b4e16
          | exact resolve b4e16 b4e1480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1480
        have b4e1716 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b4e49 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e49
        have b4e1878 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b4e12 (k X0 y)
             have i₂ := b4e1648 X0
             grind)
          | exact superpose b4e1648 b4e12
          | exact resolve b4e12 b4e1648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1648
        have b4e1887 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b4e1878 X0
             have i₂ := b4e12 X0
             grind)
          | exact superpose b4e12 b4e1878
          | exact resolve b4e1878 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1878
        have b4e1928 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b4e122 X0 y
             have i₂ := b4e1887 (σ X0)
             grind)
          | exact superpose b4e1887 b4e122
          | exact resolve b4e122 b4e1887
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e122 b4e1887
        have b4e1936 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b4e1928 X0
             have i₂ := b4e12 X0
             grind)
          | exact superpose b4e12 b4e1928
          | exact resolve b4e1928 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1928
        have b4e5355 : (σ (τ y)) ≠ (σ (τ y)) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by
          first
          | (have i₁ := b4e1716 (τ y)
             have i₂ := b4e1936 (τ y)
             grind)
          | exact superpose b4e1936 b4e1716
          | (have j0 := b4e1716 (τ y)
             grind)
          | exact resolve b4e1716 b4e1936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1716 b4e1936
        have b4e5365 : (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by grind
        clear b4e5355
        have b4e5387 : y = (M.op y y) := by
          first
          | (have i₁ := b4e5365
             have i₂ := b4e13 y
             grind)
          | exact superpose b4e13 b4e5365
          | exact resolve b4e5365 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e5365
        have b4e5410 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b4e234 X0 y
             have i₂ := b4e5387
             grind)
          | exact superpose b4e5387 b4e234
          | exact resolve b4e234 b4e5387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e234
        have b4e5602 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e5410 y
             grind)
          | exact superpose b4e5410 b4e18
          | exact resolve b4e18 b4e5410
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e5410
        have b4e5604 : False := by grind
        exact b4e5604
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op y x) := by grind
        have b5e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b5e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e21 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ x) (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e14
          | (have j0 := b5e14 (σ x) (σ y)
             grind)
          | (have r₁ := b5e14 (σ x) (σ y)
             have r₂ := b5e19
             grind)
          | exact resolve b5e14 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b5e21
        have b5e23 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e22
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e22
          | exact resolve b5e22 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22
        have b5e24 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b5e12 (k x y)
             have i₂ := b5e23
             grind)
          | exact superpose b5e23 b5e12
          | exact resolve b5e12 b5e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e25 : x = (k x y) := by
          first
          | (have i₁ := b5e24
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e24
          | exact resolve b5e24 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e60 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b5e25
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e25
          | (have j1 := b5e15 y x
             grind)
          | exact resolve b5e25 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e63 : y = (M.op y x) := by
          first
          | (have r₁ := b5e60
             have r₂ := b5e20
             grind)
          | exact resolve b5e60 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e60
        have b5e65 : False := by grind
        exact b5e65
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b6e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b6e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e17
          | exact resolve b6e17 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e22 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b6e14 y x
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e14
          | (have j0 := b6e14 y x
             grind)
          | (have r₁ := b6e14 y x
             have r₂ := b6e20
             grind)
          | exact resolve b6e14 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e23 : y = (k y x) := by grind
        clear b6e22
        have b6e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e15 (σ X0) (σ X1)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X0) (σ X1)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1638 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e53 y x
             grind)
          | exact superpose b6e53 b6e21
          | (have j1 := b6e53 y x
             grind)
          | (have r₁ := b6e21
             have r₂ := b6e53 y x
             grind)
          | exact resolve b6e21 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21 b6e53
        have b6e1652 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
        clear b6e1638
        have b6e1660 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e1652
             have i₂ := b6e23
             grind)
          | exact superpose b6e23 b6e1652
          | exact resolve b6e1652 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e1652
        have b6e1682 : False := by grind
        exact b6e1682
      · have b7e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op y x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X0 X1
             have i₂ := b7e15 (σ X0) (σ X1)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X0) (σ X1)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e793 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e46 x y
             grind)
          | exact superpose b7e46 b7e17
          | (have j1 := b7e46 x y
             grind)
          | exact resolve b7e17 b7e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e835 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b7e793
             have r₂ := b7e19
             grind)
          | exact resolve b7e793 b7e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e793
        have b7e840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b7e835
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e835
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e835 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e835
        have b7e841 : y = (M.op y x) := by grind
        clear b7e840
        have b7e842 : False := by grind
        exact b7e842
