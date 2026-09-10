import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation968`: `x = y ◇ ((z ◇ y) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation968 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law968 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law968.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e40 : (M.op x y) = (k x y) := by grind
      have b0e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e41
        | exact resolve b0e41 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e43 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e42
        | exact resolve b0e42 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e42
      have b0e44 : False := by grind
      exact b0e44
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
             have i₂ := b1e12 X0 X2 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, y = (M.op X0 (M.op (M.op y X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e12 y X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op (σ x) X0) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) X0 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op (M.op X3 X2) (M.op X3 X0)) X1 X2
             have i₂ := b1e12 X0 X2 X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op X1 y) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e27 (M.op (M.op X1 y) (M.op X1 X0))
             have i₂ := b1e12 X0 y X1
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : (M.op x y) = (k x y) := by grind
        have b1e39 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
        have b1e40 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e39
          | exact resolve b1e39 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e46 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b1e47 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e41
             have r₂ := b1e21
             grind)
          | exact resolve b1e41 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e48 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e38
             grind)
          | exact superpose b1e38 b1e48
          | exact resolve b1e48 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e48
        have b1e52 : (M.op x y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x y)
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e13
          | exact resolve b1e13 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : x = (M.op x y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e52
          | exact resolve b1e52 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e87 : ∀ X0 : G, (M.op y (M.op x (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e12
          | exact resolve b1e12 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e90 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 y) (M.op X1 X0)) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 (M.op (M.op X1 y) (M.op X1 X0))
             have i₂ := b1e12 X0 y X1
             grind)
          | exact superpose b1e12 b1e30
          | exact resolve b1e30 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e97 : ∀ X0 : G, y = (M.op (M.op y (M.op x X0)) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e90 X0 x
             have i₂ := b1e35 X0 x
             grind)
          | exact superpose b1e35 b1e90
          | exact resolve b1e90 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e90
        have b1e159 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e28 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e28
          | exact resolve b1e28 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e160 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e28 (M.op (σ y) (M.op (σ x) X0))
             have i₂ := b1e28 X0
             grind)
          | exact superpose b1e28 b1e28
          | exact resolve b1e28 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e169 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b1e159
             have i₂ := b1e160 (σ y)
             grind)
          | exact superpose b1e160 b1e159
          | exact resolve b1e159 b1e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e159 b1e160
        have b1e172 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op X1 x) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e87 (M.op (M.op X1 x) (M.op X1 X0))
             have i₂ := b1e12 X0 x X1
             grind)
          | exact superpose b1e12 b1e87
          | exact resolve b1e87 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e199 : (M.op y (M.op x (σ x))) = (M.op (M.op (σ x) y) (σ y)) := by
          first
          | (have i₁ := b1e27 (M.op (M.op (σ x) y) (σ y))
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e27
          | exact resolve b1e27 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e306 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op X1 x) (M.op X1 y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 y X1 x (M.op y X0)
             have i₂ := b1e27 X0
             grind)
          | exact superpose b1e27 b1e29
          | exact resolve b1e29 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e312 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
             have i₂ := b1e29 (M.op X1 X2) X1 X2 X0
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e323 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op x y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e306 X0 x
             have i₂ := b1e172 y x
             grind)
          | exact superpose b1e172 b1e306
          | exact resolve b1e306 b1e172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e172 b1e306
        have b1e351 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b1e323 X0
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e323
          | exact resolve b1e323 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e323
        have b1e389 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X1)) = (M.op X2 (M.op (M.op (M.op x (M.op x X0)) X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 X1 X2 (M.op x (M.op x X0)) y
             have i₂ := b1e87 X0
             grind)
          | exact superpose b1e87 b1e32
          | exact resolve b1e32 b1e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e518 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X1)) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e389 X0 X1 X2
             have i₂ := b1e312 X2 x X0
             grind)
          | exact superpose b1e312 b1e389
          | exact resolve b1e389 b1e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e389
        have b1e618 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X0)) (M.op X0 (M.op x X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e29 X0 y x X1
             have i₂ := b1e351 (M.op y X0)
             grind)
          | exact superpose b1e351 b1e29
          | exact resolve b1e29 b1e351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e351
        have b1e661 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e618 X0 X1
             have i₂ := b1e312 (M.op X0 (M.op x X1)) y X0
             grind)
          | exact superpose b1e312 b1e618
          | exact resolve b1e618 b1e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e618
        have b1e774 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) (M.op X1 x)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e661 (M.op (M.op X1 X2) (M.op X1 x)) (M.op X2 X0)
             have i₂ := b1e29 x X1 X2 X0
             grind)
          | exact superpose b1e29 b1e661
          | exact resolve b1e661 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e792 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e87 (M.op x X0)
             have i₂ := b1e661 x X0
             grind)
          | exact superpose b1e661 b1e87
          | exact resolve b1e87 b1e661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e849 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b1e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e1010 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op y X0))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e661 X1 X0
             have i₂ := b1e792 X0
             grind)
          | exact superpose b1e792 b1e661
          | exact resolve b1e661 b1e792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e661
        have b1e1033 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (M.op X2 x)) (M.op y (M.op X0 X1))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 x X2 X0 X1
             have i₂ := b1e792 (M.op X0 X1)
             grind)
          | exact superpose b1e792 b1e29
          | exact resolve b1e29 b1e792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1046 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e1033 X0 X1 x
             have i₂ := b1e774 (M.op y (M.op X0 X1)) x X0
             grind)
          | exact superpose b1e774 b1e1033
          | exact resolve b1e1033 b1e774
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774 b1e1033
        have b1e1967 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X0)) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1046 X1 (M.op (M.op X2 X1) (M.op X2 X0))
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e1046
          | exact resolve b1e1046 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1995 : (σ x) = (M.op (σ x) (M.op y (σ y))) := by
          first
          | (have i₁ := b1e1046 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1046
          | exact resolve b1e1046 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2009 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e1046 (M.op X1 y) (M.op X1 X0)
             have i₂ := b1e12 X0 y X1
             grind)
          | exact superpose b1e12 b1e1046
          | exact resolve b1e1046 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2029 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op X3 (M.op (M.op X2 X3) (M.op y (M.op X1 X0)))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e32 (M.op y (M.op X1 X0)) X3 X2 X1
             have i₂ := b1e1046 X1 X0
             grind)
          | exact superpose b1e1046 b1e32
          | exact resolve b1e32 b1e1046
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e2032 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op (M.op y X1) X0) X1 y
             have i₂ := b1e1046 (M.op y X1) X0
             grind)
          | exact superpose b1e1046 b1e12
          | exact resolve b1e12 b1e1046
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1046
        have b1e2052 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op y (M.op y (M.op X1 X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e2029 X0 X1 X2 x
             have i₂ := b1e518 X2 (M.op y (M.op X1 X0)) x
             grind)
          | exact superpose b1e518 b1e2029
          | exact resolve b1e2029 b1e518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e518 b1e2029
        have b1e2933 : y = (M.op y (M.op y y)) ∨ y = (k y (M.op y y)) := by grind
        have b1e3030 : y = (k y (M.op y y)) := by
          first
          | (have j1 := b1e849 y
             grind)
          | (have r₁ := b1e2933
             have r₂ := b1e849 y
             grind)
          | exact resolve b1e2933 b1e849
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e849 b1e2933
        have b1e3084 : y = (k y x) := by
          first
          | (have i₁ := b1e3030
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e3030
          | exact resolve b1e3030 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3030
        have b1e3972 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) y) (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e2032 X0 (M.op (M.op (σ x) y) (σ y))
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e2032
          | exact resolve b1e2032 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e4141 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e3972 X0
             have i₂ := b1e2009 (σ y) (σ x)
             grind)
          | exact superpose b1e2009 b1e3972
          | exact resolve b1e3972 b1e2009
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3972
        have b1e5584 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e82 y y
             grind)
          | exact superpose b1e82 b1e21
          | (have j1 := b1e82 y y
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e82 y x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e82 x y
             grind)
          | exact resolve b1e21 b1e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82
        have b1e5749 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e5584
        have b1e9297 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op y (M.op x X1)))) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 (M.op y (M.op x X1)) X0 X1 x
             have i₂ := b1e97 X1
             grind)
          | exact superpose b1e97 b1e29
          | exact resolve b1e29 b1e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e97
        have b1e9336 : ∀ X1 : G, x = (M.op (M.op X1 (M.op y (M.op y (M.op x X1)))) y) := by
          intro X1
          first
          | (have i₁ := b1e9297 x X1
             have i₂ := b1e1967 (M.op y (M.op x X1)) X1 x
             grind)
          | exact superpose b1e1967 b1e9297
          | exact resolve b1e9297 b1e1967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1967 b1e9297
        have b1e9400 : ∀ X1 : G, x = (M.op (M.op (M.op x X1) X1) y) := by
          intro X1
          first
          | (have i₁ := b1e9336 X1
             have i₂ := b1e2052 X1 x X1
             grind)
          | exact superpose b1e2052 b1e9336
          | exact resolve b1e9336 b1e2052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2052 b1e9336
        have b1e9459 : ∀ X1 : G, x = (M.op (M.op (M.op y X1) X1) y) := by
          intro X1
          first
          | (have i₁ := b1e9400 X1
             have i₂ := b1e792 X1
             grind)
          | exact superpose b1e792 b1e9400
          | exact resolve b1e9400 b1e792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9400
        have b1e9495 : ∀ X1 : G, x = (M.op (M.op X1 X1) y) := by
          intro X1
          first
          | (have i₁ := b1e9459 X1
             have i₂ := b1e2032 X1 X1
             grind)
          | exact superpose b1e2032 b1e9459
          | exact resolve b1e9459 b1e2032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2032 b1e9459
        have b1e9573 : x = (M.op (σ y) y) := by
          first
          | (have i₁ := b1e9495 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e9495
          | exact resolve b1e9495 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9495
        have b1e9735 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e2009 X0 (σ y)
             have i₂ := b1e9573
             grind)
          | exact superpose b1e9573 b1e2009
          | exact resolve b1e2009 b1e9573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9573
        have b1e9767 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e9735 X0
             have i₂ := b1e792 X0
             grind)
          | exact superpose b1e792 b1e9735
          | exact resolve b1e9735 b1e792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e792 b1e9735
        have b1e9853 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e312 X0 (σ y) (M.op (σ x) (σ y))
             have i₂ := b1e169
             grind)
          | exact superpose b1e169 b1e312
          | exact resolve b1e312 b1e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e169 b1e312
        have b1e10159 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e9853 X0
             have i₂ := b1e4141 X0
             grind)
          | exact superpose b1e4141 b1e9853
          | exact resolve b1e9853 b1e4141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4141 b1e9853
        have b1e10247 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (k y x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e10159 X0
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e10159
          | exact resolve b1e10159 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e10159
        have b1e10283 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e10247 X0
             have i₂ := b1e3084
             grind)
          | exact superpose b1e3084 b1e10247
          | exact resolve b1e10247 b1e3084
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3084 b1e10247
        have b1e10297 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e10283 X0
             have i₂ := b1e9767 X0
             grind)
          | exact superpose b1e9767 b1e10283
          | exact resolve b1e10283 b1e9767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10283
        have b1e10347 : (σ x) = (M.op y (M.op y (σ y))) := by
          first
          | (have i₁ := b1e1995
             have i₂ := b1e10297 (M.op y (σ y))
             grind)
          | exact superpose b1e10297 b1e1995
          | exact resolve b1e1995 b1e10297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1995
        have b1e10348 : (σ y) = (M.op y (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e10297 (σ x)
             grind)
          | exact superpose b1e10297 b1e22
          | exact resolve b1e22 b1e10297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e10350 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e10297 (σ y)
             grind)
          | exact superpose b1e10297 b1e19
          | exact resolve b1e19 b1e10297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10297
        have b1e10496 : (σ x) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b1e10350
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e10350
          | exact resolve b1e10350 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e10350
        have b1e11191 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e1010 (σ x) X0
             have i₂ := b1e10348
             grind)
          | exact superpose b1e10348 b1e1010
          | exact resolve b1e1010 b1e10348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1010 b1e10348
        have b1e50208 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e5749
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e5749
          | (have j1 := b1e17 (σ y) (σ y)
             grind)
          | exact resolve b1e5749 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5749
        have b1e50217 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b1e50208
        have b1e50232 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e50217
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e50217
          | exact resolve b1e50217 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50217
        have b1e50233 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b1e50232
        have b1e50246 : (σ y) = (M.op y (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e50233
             have i₂ := b1e9767 (σ y)
             grind)
          | exact superpose b1e9767 b1e50233
          | exact resolve b1e50233 b1e9767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9767 b1e50233
        have b1e50256 : (σ y) = (M.op y (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e50246
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e50246
          | exact resolve b1e50246 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50246
        have b1e50283 : (σ x) = (M.op y (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e11191 y
             have i₂ := b1e50256
             grind)
          | exact superpose b1e50256 b1e11191
          | exact resolve b1e11191 b1e50256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11191 b1e50256
        have b1e50349 : x = y := by
          first
          | (have r₁ := b1e50283
             have r₂ := b1e10496
             grind)
          | exact resolve b1e50283 b1e10496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10496 b1e50283
        have b1e52596 : (M.op y (M.op y (σ y))) = (M.op (M.op (σ y) y) (σ y)) := by
          first
          | (have i₁ := b1e199
             have i₂ := b1e50349
             grind)
          | exact superpose b1e50349 b1e199
          | exact resolve b1e199 b1e50349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199 b1e50349
        have b1e52631 : (M.op (σ y) (σ y)) = (M.op y (M.op y (σ y))) := by
          first
          | (have i₁ := b1e52596
             have i₂ := b1e2009 (σ y) (σ y)
             grind)
          | exact superpose b1e2009 b1e52596
          | exact resolve b1e52596 b1e2009
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2009 b1e52596
        have b1e52659 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e52631
             have i₂ := b1e10347
             grind)
          | exact superpose b1e10347 b1e52631
          | exact resolve b1e52631 b1e10347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10347 b1e52631
        have b1e52676 : False := by grind
        exact b1e52676
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
             have i₂ := b2e12 X0 X2 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X3 X2) (M.op X3 X0)) X1 X2
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b2e27 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e27
          | exact resolve b2e27 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e27 (M.op x (M.op y X0))
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e27
          | exact resolve b2e27 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op X1 y) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e27 (M.op (M.op X1 y) (M.op X1 X0))
             have i₂ := b2e12 X0 y X1
             grind)
          | exact superpose b2e12 b2e27
          | exact resolve b2e27 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))) = X1 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          grind
        have b2e41 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b2e42 : (M.op x x) = (M.op y (M.op x y)) := by
          first
          | (have i₁ := b2e27 (M.op x x)
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e27
          | exact resolve b2e27 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ x) (σ x)) x
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e135 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X0)) (M.op X0 (M.op (M.op x x) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 y (M.op x x) X1
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e28
          | exact resolve b2e28 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e182 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
             have i₂ := b2e28 (M.op X1 X2) X1 X2 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e197 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op x x) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e135 X0 X1
             have i₂ := b2e182 (M.op X0 (M.op (M.op x x) X1)) y X0
             grind)
          | exact superpose b2e182 b2e135
          | exact resolve b2e135 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e135
        have b2e221 : ∀ X0 X1 X2 : G, (M.op (M.op y X1) X0) = (M.op X2 (M.op (M.op X1 X2) (M.op x (M.op y X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e30 (M.op x (M.op y X0)) X2 X1 y
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e30
          | exact resolve b2e30 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e263 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 X1 x
             have i₂ := b2e30 X2 X0 X1 x
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e264 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
          intro X0 X1
          grind
        have b2e277 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 x X1
             have i₂ := b2e30 (M.op X1 X2) x X1 X0
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e299 : ∀ X0 X1 X2 : G, (M.op (M.op y X1) X0) = (M.op X2 (M.op (M.op X1 X2) (M.op y (M.op x X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e221 X0 X1 X2
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e221
          | exact resolve b2e221 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e221
        have b2e463 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 X0
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e27
          | exact resolve b2e27 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e466 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op (M.op x X1) (M.op y (M.op x X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op y X0) X1 x
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e473 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b2e466 X0 x
             have i₂ := b2e299 X0 x x
             grind)
          | exact superpose b2e299 b2e466
          | exact resolve b2e466 b2e299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299 b2e466
        have b2e490 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e41 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e500 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op X1 y) (M.op X1 y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 y X1 y (M.op x X0)
             have i₂ := b2e463 X0
             grind)
          | exact superpose b2e463 b2e28
          | exact resolve b2e28 b2e463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e512 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
          intro X0
          first
          | (have i₁ := b2e500 X0 x
             have i₂ := b2e33 y x
             grind)
          | exact superpose b2e33 b2e500
          | exact resolve b2e500 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e500
        have b2e514 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e512 X0
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e512
          | exact resolve b2e512 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e512
        have b2e601 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op X1 (M.op (M.op x X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e30 X0 X1 x y
             have i₂ := b2e473 (M.op y X0)
             grind)
          | exact superpose b2e473 b2e30
          | exact resolve b2e30 b2e473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e602 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X0)) (M.op X0 (M.op x X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 y x X1
             have i₂ := b2e473 (M.op y X0)
             grind)
          | exact superpose b2e473 b2e28
          | exact resolve b2e28 b2e473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e473
        have b2e642 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e602 X0 X1
             have i₂ := b2e182 (M.op X0 (M.op x X1)) y X0
             grind)
          | exact superpose b2e182 b2e602
          | exact resolve b2e602 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e602
        have b2e670 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X1) X0)) = (M.op x (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e30 X0 X1 x x
             have i₂ := b2e514 (M.op x X0)
             grind)
          | exact superpose b2e514 b2e30
          | exact resolve b2e30 b2e514
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e514
        have b2e713 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e670 X0 x
             have i₂ := b2e601 X0 x
             grind)
          | exact superpose b2e601 b2e670
          | exact resolve b2e670 b2e601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e601 b2e670
        have b2e730 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b2e62 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e731 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e730
             have r₂ := b2e21
             grind)
          | exact resolve b2e730 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e730
        have b2e732 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e731
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e731
          | exact resolve b2e731 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e731
        have b2e806 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e807 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e806 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e806
        have b2e868 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X2 (M.op x X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X2 (M.op x X0)) X1 X2
             have i₂ := b2e642 X2 X0
             grind)
          | exact superpose b2e642 b2e12
          | exact resolve b2e12 b2e642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e871 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X3)) (M.op X3 X0)) = (M.op X2 (M.op x X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e28 X3 X1 X2 (M.op X2 (M.op x X0))
             have i₂ := b2e642 X2 X0
             grind)
          | exact superpose b2e642 b2e28
          | exact resolve b2e28 b2e642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e642
        have b2e1054 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 ∨ y = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e40 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40
          | exact resolve b2e40 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e1117 : ∀ X0 : G, (M.op y (M.op x (M.op x X0))) = X0 ∨ y = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e1054 X0
             have i₂ := b2e32 (M.op x X0)
             grind)
          | exact superpose b2e32 b2e1054
          | exact resolve b2e1054 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e1054
        have b2e1128 : ∀ X0 : G, (M.op y (M.op y (M.op y X0))) = X0 ∨ y = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e1117 X0
             have i₂ := b2e713 X0
             grind)
          | exact superpose b2e713 b2e1117
          | exact resolve b2e1117 b2e713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e713 b2e1117
        have b2e1140 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e732
             grind)
          | exact superpose b2e732 b2e19
          | exact resolve b2e19 b2e732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e732
        have b2e2844 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e71 y y
             grind)
          | exact superpose b2e71 b2e21
          | (have j1 := b2e71 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e71 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e71 x y
             grind)
          | exact resolve b2e21 b2e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e2993 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2844
        have b2e3499 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e182 X1 y (M.op x X0)
             have i₂ := b2e463 X0
             grind)
          | exact superpose b2e463 b2e182
          | exact resolve b2e182 b2e463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e463
        have b2e3535 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X1 X0) X1
             have i₂ := b2e182 (M.op X1 X2) X1 X0
             grind)
          | exact superpose b2e182 b2e12
          | exact resolve b2e12 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3563 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X3 (M.op X3 X0))) (M.op X2 X4)) (M.op X4 (M.op X0 X1))) = X1 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e28 X4 X2 (M.op X3 (M.op X3 X0)) X1
             have i₂ := b2e182 X1 X3 X0
             grind)
          | exact superpose b2e182 b2e28
          | exact resolve b2e28 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e3566 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X2 X0)) X3) (M.op X0 X1)) = (M.op X4 (M.op (M.op X3 X4) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e30 X1 X4 X3 (M.op X2 (M.op X2 X0))
             have i₂ := b2e182 X1 X2 X0
             grind)
          | exact superpose b2e182 b2e30
          | exact resolve b2e30 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3606 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X2 X0)) X3) (M.op X0 X1)) = (M.op X3 (M.op x X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e3566 X0 X1 X2 X3 x
             have i₂ := b2e868 X1 x X3
             grind)
          | exact superpose b2e868 b2e3566
          | exact resolve b2e3566 b2e868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3566
        have b2e3609 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X3 X0)) (M.op x (M.op X0 X1))) = X1 := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e3563 X0 X1 x X3 x
             have i₂ := b2e871 (M.op X0 X1) x (M.op X3 (M.op X3 X0)) x
             grind)
          | exact superpose b2e871 b2e3563
          | exact resolve b2e3563 b2e871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e871 b2e3563
        have b2e3667 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x X1)) = (M.op (M.op X0 X3) (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e3606 X0 X1 x X3
             have i₂ := b2e182 X3 x X0
             grind)
          | exact superpose b2e182 b2e3606
          | exact resolve b2e3606 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3606
        have b2e3669 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e3609 X0 X1 x
             have i₂ := b2e182 (M.op x (M.op X0 X1)) x X0
             grind)
          | exact superpose b2e182 b2e3609
          | exact resolve b2e3609 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3609
        have b2e4007 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e3669 X1 (M.op x (M.op X1 X0))
             have i₂ := b2e3669 X1 X0
             grind)
          | exact superpose b2e3669 b2e3669
          | exact resolve b2e3669 b2e3669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4076 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op (M.op (M.op x (M.op X1 X0)) X3) X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e30 X2 X3 (M.op x (M.op X1 X0)) X1
             have i₂ := b2e3669 X1 X0
             grind)
          | exact superpose b2e3669 b2e30
          | exact resolve b2e30 b2e3669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3669
        have b2e4122 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op x (M.op X1 X0)) (M.op x X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4076 X0 X1 X2 x
             have i₂ := b2e868 X2 x (M.op x (M.op X1 X0))
             grind)
          | exact superpose b2e868 b2e4076
          | exact resolve b2e4076 b2e868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4076
        have b2e4154 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x (M.op (M.op x (M.op X1 X0)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4122 X0 X1 X2
             have i₂ := b2e4007 X2 (M.op x (M.op X1 X0))
             grind)
          | exact superpose b2e4007 b2e4122
          | exact resolve b2e4122 b2e4007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4122
        have b2e4159 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x (M.op (M.op X1 X0) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4154 X0 X1 X2
             have i₂ := b2e3499 (M.op X1 X0) X2
             grind)
          | exact superpose b2e3499 b2e4154
          | exact resolve b2e4154 b2e3499
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4154
        have b2e6650 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X4)) = (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e30 X4 (M.op X2 (M.op X3 X0)) (M.op X2 X3) X1
             have i₂ := b2e277 X2 X3 X0
             grind)
          | exact superpose b2e277 b2e30
          | exact resolve b2e30 b2e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e6651 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 X0)) X4) X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e30 X3 X4 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
             have i₂ := b2e277 X1 X2 X0
             grind)
          | exact superpose b2e277 b2e30
          | exact resolve b2e30 b2e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e6661 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op X1 X2) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e182 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
             have i₂ := b2e277 X1 X2 X0
             grind)
          | exact superpose b2e277 b2e182
          | exact resolve b2e182 b2e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182 b2e277
        have b2e6668 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X1 (M.op X2 X0)) (M.op x X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e6651 X0 X1 X2 X3 x
             have i₂ := b2e868 X3 x (M.op X1 (M.op X2 X0))
             grind)
          | exact superpose b2e868 b2e6651
          | exact resolve b2e6651 b2e868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e868 b2e6651
        have b2e6669 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) = (M.op (M.op X2 X3) (M.op x X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e6650 X0 x X2 X3 X4
             have i₂ := b2e3667 x X4 (M.op X2 X3)
             grind)
          | (have i₁ := b2e6650 X0 x X2 X3 x
             have i₂ := b2e3667 X0 x (M.op x (M.op X2 X3))
             grind)
          | exact superpose b2e3667 b2e6650
          | exact resolve b2e6650 b2e3667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3667 b2e6650
        have b2e6819 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op x (M.op (M.op X1 (M.op X2 X0)) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e6668 X0 X1 X2 X3
             have i₂ := b2e4007 X3 (M.op X1 (M.op X2 X0))
             grind)
          | exact superpose b2e4007 b2e6668
          | exact resolve b2e6668 b2e4007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6668
        have b2e6820 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) = (M.op x (M.op (M.op X2 X3) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e6669 X0 X2 X3 X4
             have i₂ := b2e4007 X4 (M.op X2 X3)
             grind)
          | exact superpose b2e4007 b2e6669
          | exact resolve b2e6669 b2e4007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4007 b2e6669
        have b2e6878 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X2 X0) (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e6819 X0 X1 X2 X3
             have i₂ := b2e4159 (M.op X2 X0) X1 X3
             grind)
          | exact superpose b2e4159 b2e6819
          | exact resolve b2e6819 b2e4159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6819
        have b2e6879 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e6820 X0 X2 X3 X4
             have i₂ := b2e4159 X3 X2 X4
             grind)
          | exact superpose b2e4159 b2e6820
          | exact resolve b2e6820 b2e4159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4159 b2e6820
        have b2e6896 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 X2) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e6879 X0 X2 X3 X4
             have i₂ := b2e6878 (M.op X3 X0) X0 X2 X4
             grind)
          | exact superpose b2e6878 b2e6879
          | exact resolve b2e6879 b2e6878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6879
        have b2e6906 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e6896 X0 X2 X3 X4
             have i₂ := b2e6878 X0 (M.op X0 X2) X3 X4
             grind)
          | exact superpose b2e6878 b2e6896
          | exact resolve b2e6896 b2e6878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6896
        have b2e6908 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op X0 (M.op (M.op X0 (M.op X2 X3)) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e6906 X0 X2 X3 X4
             have i₂ := b2e6661 X3 X0 X2 X4
             grind)
          | exact superpose b2e6661 b2e6906
          | exact resolve b2e6906 b2e6661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6906
        have b2e10535 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op x x) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e263 X2 X1 (M.op (M.op X1 X2) (M.op (M.op x x) X0))
             have i₂ := b2e197 (M.op X1 X2) X0
             grind)
          | exact superpose b2e197 b2e263
          | exact resolve b2e263 b2e197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e197 b2e263
        have b2e10569 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op (M.op (M.op x x) X1) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e10535 X0 X1 X2
             have i₂ := b2e6878 X2 (M.op x x) X1 X0
             grind)
          | exact superpose b2e6878 b2e10535
          | exact resolve b2e10535 b2e6878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6878 b2e10535
        have b2e10678 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op (M.op x (M.op x X1)) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e10569 X0 X1 X2
             have i₂ := b2e6661 X1 x x X0
             grind)
          | exact superpose b2e6661 b2e10569
          | exact resolve b2e10569 b2e6661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6661 b2e10569
        have b2e10741 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op (M.op x X1) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e10678 X0 X1 X2
             have i₂ := b2e3499 (M.op x X1) X0
             grind)
          | exact superpose b2e3499 b2e10678
          | exact resolve b2e10678 b2e3499
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10678
        have b2e10792 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e10741 X0 X1 X2
             have i₂ := b2e3499 X1 X0
             grind)
          | exact superpose b2e3499 b2e10741
          | exact resolve b2e10741 b2e3499
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3499 b2e10741
        have b2e13537 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X0)) (M.op X0 X4)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e30 X4 (M.op X3 (M.op X2 X0)) (M.op X2 X3) X1
             have i₂ := b2e3535 X3 X2 X0
             grind)
          | exact superpose b2e3535 b2e30
          | exact resolve b2e30 b2e3535
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e3535
        have b2e13567 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X0)) (M.op X0 X4)) = (M.op X1 (M.op (M.op X1 (M.op X2 X3)) X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e13537 X0 X1 X2 X3 X4
             have i₂ := b2e10792 X4 (M.op X1 (M.op X2 X3)) X1
             grind)
          | (have i₁ := b2e13537 X0 X1 X2 X3 X4
             have i₂ := b2e10792 X4 X1 (M.op X1 (M.op X2 X3))
             grind)
          | exact superpose b2e10792 b2e13537
          | exact resolve b2e13537 b2e10792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13537
        have b2e13773 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op X3 (M.op X2 X0)) (M.op X0 X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e13567 X0 x X2 X3 X4
             have i₂ := b2e6908 x X2 X3 X4
             grind)
          | exact superpose b2e6908 b2e13567
          | exact resolve b2e13567 b2e6908
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6908 b2e13567
        have b2e13900 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op X0 (M.op (M.op X3 (M.op X2 X0)) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b2e13773 X0 X2 X3 X4
             have i₂ := b2e10792 X4 (M.op X3 (M.op X2 X0)) X0
             grind)
          | (have i₁ := b2e13773 X0 X2 X3 X4
             have i₂ := b2e10792 X4 X0 (M.op X3 (M.op X2 X0))
             grind)
          | exact superpose b2e10792 b2e13773
          | exact resolve b2e13773 b2e10792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13773
        have b2e35250 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e2993
             have i₂ := b2e807 y
             grind)
          | exact superpose b2e807 b2e2993
          | (have j1 := b2e807 (σ y)
             grind)
          | exact resolve b2e2993 b2e807
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2993
        have b2e35252 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e35250
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e35250
          | exact resolve b2e35250 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35250
        have b2e35253 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e35252
        have b2e35270 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e35253
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e35253
          | exact resolve b2e35253 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35253
        have b2e35303 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e35270
             grind)
          | exact superpose b2e35270 b2e21
          | exact resolve b2e21 b2e35270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35329 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e490 (σ y)
             have i₂ := b2e35270
             grind)
          | exact superpose b2e35270 b2e490
          | exact resolve b2e490 b2e35270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35412 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have r₁ := b2e35329
             have r₂ := b2e35270
             grind)
          | exact resolve b2e35329 b2e35270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35270 b2e35329
        have b2e35452 : (σ y) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e35412
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e35412
          | exact resolve b2e35412 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35412
        have b2e36429 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) (M.op X0 y)) ∨ y = (k y (M.op y y)) ∨ y = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e264 (M.op y (M.op y X0)) y
             have i₂ := b2e1128 X0
             grind)
          | exact superpose b2e1128 b2e264
          | (have j0 := b2e264 X0 y
             grind)
          | exact resolve b2e264 b2e1128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e264 b2e1128
        have b2e36816 : ∀ X0 : G, y = (M.op X0 (M.op (M.op y (M.op y X0)) y)) ∨ y = (k y (M.op y y)) ∨ y = (k y x) := by
          intro X0
          first
          | (have i₁ := b2e36429 X0
             have i₂ := b2e10792 y (M.op y (M.op y X0)) X0
             grind)
          | (have i₁ := b2e36429 X0
             have i₂ := b2e10792 y X0 (M.op y (M.op y X0))
             grind)
          | exact superpose b2e10792 b2e36429
          | exact resolve b2e36429 b2e10792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10792 b2e36429
        have b2e37008 : y = (M.op y (M.op y y)) ∨ y = (k y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e36816 x
             have i₂ := b2e13900 x y y y
             grind)
          | exact superpose b2e13900 b2e36816
          | exact resolve b2e36816 b2e13900
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13900 b2e36816
        have b2e37157 : y = (k y (M.op y y)) ∨ y = (k y x) := by
          first
          | (have j1 := b2e490 y
             grind)
          | (have r₁ := b2e37008
             have r₂ := b2e490 y
             grind)
          | exact resolve b2e37008 b2e490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e490 b2e37008
        have b2e37269 : y = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e37157
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e37157
          | exact resolve b2e37157 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37157
        have b2e37270 : y = (k y x) := by grind
        clear b2e37269
        have b2e37378 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e1140
             have i₂ := b2e37270
             grind)
          | exact superpose b2e37270 b2e1140
          | exact resolve b2e1140 b2e37270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1140 b2e37270
        have b2e40571 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e35452
             have i₂ := b2e807 y
             grind)
          | exact superpose b2e807 b2e35452
          | (have j1 := b2e807 y
             grind)
          | exact resolve b2e35452 b2e807
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e807 b2e35452
        have b2e40606 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e40571
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40571
          | exact resolve b2e40571 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40571
        have b2e40616 : x = y ∨ y = (M.op y y) := by
          first
          | (have r₁ := b2e40606
             have r₂ := b2e35303
             grind)
          | exact resolve b2e40606 b2e35303
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35303 b2e40606
        have b2e40626 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e40616
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40616
          | exact resolve b2e40616 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40616
        have b2e40627 : x = y := by grind
        clear b2e40626
        have b2e44027 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e37378
             have i₂ := b2e40627
             grind)
          | exact superpose b2e40627 b2e37378
          | exact resolve b2e37378 b2e40627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37378
        have b2e44028 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e44027
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e44027
          | exact resolve b2e44027 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44027
        have b2e44056 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e44028
             have i₂ := b2e40627
             grind)
          | exact superpose b2e40627 b2e44028
          | exact resolve b2e44028 b2e40627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40627 b2e44028
        have b2e44057 : False := by grind
        exact b2e44057
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
             have i₂ := b3e12 X0 X2 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, x = (M.op X0 (M.op (M.op x X0) y)) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ y) X0) (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op (M.op X3 X2) (M.op X3 X0)) X1 X2
             have i₂ := b3e12 X0 X2 X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e27 (M.op y (M.op x X0))
             have i₂ := b3e27 X0
             grind)
          | exact superpose b3e27 b3e27
          | exact resolve b3e27 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 x) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e27 (M.op (M.op X1 x) (M.op X1 X0))
             have i₂ := b3e12 X0 x X1
             grind)
          | exact superpose b3e12 b3e27
          | exact resolve b3e27 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (k y x) = (M.op y x) := by grind
        have b3e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e40
          | exact resolve b3e40 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e43 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e47 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b3e48 : x = (k x y) := by
          first
          | (have r₁ := b3e43
             have r₂ := b3e20
             grind)
          | exact resolve b3e43 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e17 (σ X1) (σ X0)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e89 : ∀ X0 X1 : G, (M.op (M.op x X1) y) = (M.op X0 (M.op (M.op X1 X0) x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op (M.op x X1) y) X0 X1
             have i₂ := b3e30 X1
             grind)
          | exact superpose b3e30 b3e12
          | exact resolve b3e12 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e116 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e19
          | exact resolve b3e19 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e121 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e116
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e116
          | exact resolve b3e116 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e151 : (M.op (M.op (σ y) x) (σ x)) = (M.op x (M.op y (σ y))) := by
          first
          | (have i₁ := b3e27 (M.op (M.op (σ y) x) (σ x))
             have i₂ := b3e31 x
             grind)
          | exact superpose b3e31 b3e27
          | exact resolve b3e27 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e152 : (M.op (M.op (σ y) x) (σ x)) = (M.op y (M.op x (σ y))) := by
          first
          | (have i₁ := b3e151
             have i₂ := b3e34 (σ y)
             grind)
          | exact superpose b3e34 b3e151
          | exact resolve b3e151 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e151
        have b3e204 : ∀ X0 X1 : G, (M.op (M.op (σ (k x y)) (M.op (σ x) X0)) (M.op X0 (M.op (σ y) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X0 (σ x) (σ y) X1
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e29
          | exact resolve b3e29 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e242 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op x X1)) (M.op X0 X1)) x) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X1 X0 (M.op x X1) y
             have i₂ := b3e30 X1
             grind)
          | exact superpose b3e30 b3e29
          | exact resolve b3e29 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e254 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
             have i₂ := b3e29 (M.op X1 X2) X1 X2 X0
             grind)
          | exact superpose b3e29 b3e12
          | exact resolve b3e12 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e274 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) X0)) (M.op X0 (M.op (σ y) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e204 X0 X1
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e204
          | exact resolve b3e204 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e204
        have b3e280 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ y) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e274 X0 X1
             have i₂ := b3e254 (M.op X0 (M.op (σ y) X1)) (σ x) X0
             grind)
          | exact superpose b3e254 b3e274
          | exact resolve b3e274 b3e254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e274
        have b3e359 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 X1 x
             have i₂ := b3e32 X2 X0 X1 x
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e373 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 x X1
             have i₂ := b3e32 (M.op X1 X2) x X1 X0
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e412 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e280 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e280
          | exact resolve b3e280 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e425 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) (M.op X1 (σ y))) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e280 (M.op (M.op X1 X2) (M.op X1 (σ y))) (M.op X2 X0)
             have i₂ := b3e29 (σ y) X1 X2 X0
             grind)
          | exact superpose b3e29 b3e280
          | exact resolve b3e280 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e428 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X2 (M.op (σ y) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X2 (M.op (σ y) X0)) X1 X2
             have i₂ := b3e280 X2 X0
             grind)
          | exact superpose b3e280 b3e12
          | exact resolve b3e12 b3e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e486 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 X1)) = (M.op X2 (M.op (M.op (M.op X0 (σ x)) X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e32 X1 X2 (M.op X0 (σ x)) X0
             have i₂ := b3e412 X0
             grind)
          | exact superpose b3e412 b3e32
          | exact resolve b3e32 b3e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e498 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (M.op X0 (σ x)) (M.op (σ y) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e486 X0 X1 x
             have i₂ := b3e428 X1 x (M.op X0 (σ x))
             grind)
          | exact superpose b3e428 b3e486
          | exact resolve b3e486 b3e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e486
        have b3e574 : ∀ X0 : G, (M.op y (M.op x (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e27 X0
             have i₂ := b3e34 (M.op x X0)
             grind)
          | exact superpose b3e34 b3e27
          | exact resolve b3e27 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e34
        have b3e695 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e574 (M.op (σ y) X0)
             have i₂ := b3e280 x X0
             grind)
          | exact superpose b3e280 b3e574
          | exact resolve b3e574 b3e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e696 : (σ x) = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e574 (σ x)
             have i₂ := b3e412 x
             grind)
          | exact superpose b3e412 b3e574
          | exact resolve b3e574 b3e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e412
        have b3e699 : ∀ X0 X1 : G, (M.op (M.op x (M.op x X0)) (M.op X0 (M.op y X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 (M.op x (M.op x X0)) y
             have i₂ := b3e574 X0
             grind)
          | exact superpose b3e574 b3e12
          | exact resolve b3e12 b3e574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e706 : ∀ X0 X1 X2 : G, (M.op (M.op y X1) X0) = (M.op X2 (M.op (M.op X1 X2) (M.op x (M.op x X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e32 (M.op x (M.op x X0)) X2 X1 y
             have i₂ := b3e574 X0
             grind)
          | exact superpose b3e574 b3e32
          | exact resolve b3e32 b3e574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e707 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X1 (M.op (σ y) (M.op x (M.op x X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e706 X0 X1 x
             have i₂ := b3e428 (M.op x (M.op x X0)) x X1
             grind)
          | exact superpose b3e428 b3e706
          | exact resolve b3e706 b3e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e706
        have b3e714 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e699 X0 X1
             have i₂ := b3e254 (M.op X0 (M.op y X1)) x X0
             grind)
          | exact superpose b3e254 b3e699
          | exact resolve b3e699 b3e254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e699
        have b3e716 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X1 (M.op y (M.op x (M.op x X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e707 X0 X1
             have i₂ := b3e695 (M.op x (M.op x X0))
             grind)
          | exact superpose b3e695 b3e707
          | exact resolve b3e707 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e707
        have b3e721 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e716 X0 X1
             have i₂ := b3e574 X0
             grind)
          | exact superpose b3e574 b3e716
          | exact resolve b3e716 b3e574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e574 b3e716
        have b3e735 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b3e47 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e754 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) (σ x)) (M.op (σ y) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e29 (σ y) y X0 X1
             have i₂ := b3e696
             grind)
          | exact superpose b3e696 b3e29
          | exact resolve b3e29 b3e696
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e696
        have b3e765 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e754 X0 X1
             have i₂ := b3e498 (M.op y X0) (M.op X0 X1)
             grind)
          | exact superpose b3e498 b3e754
          | exact resolve b3e754 b3e498
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e498 b3e754
        have b3e771 : ∀ X0 X1 : G, (M.op y (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e765 X0 X1
             have i₂ := b3e695 (M.op (M.op y X0) (M.op X0 X1))
             grind)
          | exact superpose b3e695 b3e765
          | exact resolve b3e765 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e765
        have b3e774 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e771 X0 X1
             have i₂ := b3e721 (M.op X0 X1) X0
             grind)
          | exact superpose b3e721 b3e771
          | exact resolve b3e771 b3e721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e771
        have b3e918 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (M.op X2 (σ y))) (M.op y (M.op X0 X1))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e29 (σ y) X2 X0 X1
             have i₂ := b3e695 (M.op X0 X1)
             grind)
          | exact superpose b3e695 b3e29
          | exact resolve b3e29 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e929 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e918 X0 X1 x
             have i₂ := b3e425 (M.op y (M.op X0 X1)) x X0
             grind)
          | exact superpose b3e425 b3e918
          | exact resolve b3e918 b3e425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e425 b3e918
        have b3e1886 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X0)) = (M.op y (M.op X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e774 X1 (M.op (M.op X2 X1) (M.op X2 X0))
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e774
          | exact resolve b3e774 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1892 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e774 X1 (M.op X1 (M.op y X0))
             have i₂ := b3e714 X1 X0
             grind)
          | exact superpose b3e714 b3e774
          | exact resolve b3e774 b3e714
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2409 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op (M.op (M.op y (M.op X1 X0)) X3) X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e32 X2 X3 (M.op y (M.op X1 X0)) X1
             have i₂ := b3e929 X1 X0
             grind)
          | exact superpose b3e929 b3e32
          | exact resolve b3e32 b3e929
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e929
        have b3e2444 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op y (M.op X1 X0)) (M.op (σ y) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e2409 X0 X1 X2 x
             have i₂ := b3e428 X2 x (M.op y (M.op X1 X0))
             grind)
          | exact superpose b3e428 b3e2409
          | exact resolve b3e2409 b3e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2409
        have b3e2479 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X0) (M.op (σ y) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e2444 X0 X1 X2
             have i₂ := b3e721 (M.op (σ y) X2) (M.op X1 X0)
             grind)
          | exact superpose b3e721 b3e2444
          | exact resolve b3e2444 b3e721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2444
        have b3e2495 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X0) (M.op y X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e2479 X0 X1 X2
             have i₂ := b3e695 X2
             grind)
          | exact superpose b3e695 b3e2479
          | exact resolve b3e2479 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2479
        have b3e2501 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y (M.op (M.op X1 X0) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e2495 X0 X1 X2
             have i₂ := b3e1892 X2 (M.op X1 X0)
             grind)
          | exact superpose b3e1892 b3e2495
          | exact resolve b3e2495 b3e1892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2495
        have b3e5376 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e76 y y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e76
          | exact resolve b3e76 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e5659 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b3e5376
        have b3e9694 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 (M.op y X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e254 X2 X1 (M.op X1 (M.op y X0))
             have i₂ := b3e714 X1 X0
             grind)
          | exact superpose b3e714 b3e254
          | exact resolve b3e254 b3e714
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e9744 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op (M.op X4 X2) (M.op X4 X1)) X0) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e254 X3 (M.op (M.op X4 X2) (M.op X4 X1)) (M.op X1 (M.op X2 X0))
             have i₂ := b3e29 X1 X4 X2 X0
             grind)
          | exact superpose b3e29 b3e254
          | exact resolve b3e254 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e254
        have b3e10034 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op y (M.op X2 X1)) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e9744 X0 X1 X2 X3 x
             have i₂ := b3e1886 X1 X2 x
             grind)
          | exact superpose b3e1886 b3e9744
          | exact resolve b3e9744 b3e1886
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9744
        have b3e10104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op X2 X1) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e10034 X0 X1 X2 X3
             have i₂ := b3e721 X0 (M.op X2 X1)
             grind)
          | exact superpose b3e721 b3e10034
          | exact resolve b3e10034 b3e721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10034
        have b3e10333 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 (σ y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e280 X1 (M.op (M.op X1 (σ y)) X0)
             have i₂ := b3e359 (σ y) X1 X0
             grind)
          | exact superpose b3e359 b3e280
          | exact resolve b3e280 b3e359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e280
        have b3e11321 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 X0)) X4) X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e32 X3 X4 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
             have i₂ := b3e373 X1 X2 X0
             grind)
          | exact superpose b3e373 b3e32
          | exact resolve b3e32 b3e373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e373
        have b3e11338 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (σ y) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11321 X0 X1 X2 X3 x
             have i₂ := b3e428 X3 x (M.op X1 (M.op X2 X0))
             grind)
          | exact superpose b3e428 b3e11321
          | exact resolve b3e11321 b3e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e428 b3e11321
        have b3e11533 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X1 (M.op X2 X0)) (M.op y X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11338 X0 X1 X2 X3
             have i₂ := b3e695 X3
             grind)
          | exact superpose b3e695 b3e11338
          | exact resolve b3e11338 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11338
        have b3e11629 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op (M.op X1 (M.op X2 X0)) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11533 X0 X1 X2 X3
             have i₂ := b3e1892 X3 (M.op X1 (M.op X2 X0))
             grind)
          | exact superpose b3e1892 b3e11533
          | exact resolve b3e11533 b3e1892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1892 b3e11533
        have b3e11676 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X2 X0) (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11629 X0 X1 X2 X3
             have i₂ := b3e2501 (M.op X2 X0) X1 X3
             grind)
          | exact superpose b3e2501 b3e11629
          | exact resolve b3e11629 b3e2501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11629
        have b3e11799 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ y) (σ y))) := by grind
        have b3e11970 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) := by
          first
          | (have j1 := b3e735 (σ y)
             grind)
          | (have r₁ := b3e11799
             have r₂ := b3e735 (σ y)
             grind)
          | exact resolve b3e11799 b3e735
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e735 b3e11799
        have b3e12107 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e11970
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e11970
          | exact resolve b3e11970 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11970
        have b3e12190 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e12107
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e12107
          | exact resolve b3e12107 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12107
        have b3e12242 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e12190
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e12190
          | exact resolve b3e12190 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e12190
        have b3e12586 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op y x)
             have i₂ := b3e12242
             grind)
          | exact superpose b3e12242 b3e13
          | exact resolve b3e13 b3e12242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12242
        have b3e12603 : y = (M.op y x) := by
          first
          | (have i₁ := b3e12586
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e12586
          | exact resolve b3e12586 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12586
        have b3e13039 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e721 X0 x
             have i₂ := b3e12603
             grind)
          | exact superpose b3e12603 b3e721
          | exact resolve b3e721 b3e12603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13040 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e714 X0 x
             have i₂ := b3e12603
             grind)
          | exact superpose b3e12603 b3e714
          | exact resolve b3e714 b3e12603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e714 b3e12603
        have b3e13153 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e121
             have i₂ := b3e13039 y
             grind)
          | exact superpose b3e13039 b3e121
          | exact resolve b3e121 b3e13039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13473 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e774 X0 (M.op X0 y)
             have i₂ := b3e13040 X0
             grind)
          | exact superpose b3e13040 b3e774
          | exact resolve b3e774 b3e13040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e774
        have b3e13484 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op X0 (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e359 X1 X0 (M.op (M.op X0 X1) y)
             have i₂ := b3e13040 (M.op X0 X1)
             grind)
          | exact superpose b3e13040 b3e359
          | exact resolve b3e359 b3e13040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e359
        have b3e13648 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e5659
             have i₂ := b3e17 y y
             grind)
          | exact superpose b3e17 b3e5659
          | (have j1 := b3e17 y y
             grind)
          | exact resolve b3e5659 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5659
        have b3e13666 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
        clear b3e13648
        have b3e13684 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e13666
             have r₂ := b3e13153
             grind)
          | exact resolve b3e13666 b3e13153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13153 b3e13666
        have b3e13992 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op (M.op X2 X0) (M.op (M.op x (M.op y X0)) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e32 X3 (M.op X2 X0) (M.op X2 x) X1
             have i₂ := b3e35 X0 X2
             grind)
          | exact superpose b3e35 b3e32
          | exact resolve b3e32 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e14016 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op X0 (M.op (M.op (M.op x (M.op y X0)) X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e13992 X0 X1 X2 X3
             have i₂ := b3e11676 X0 (M.op x (M.op y X0)) X2 X3
             grind)
          | exact superpose b3e11676 b3e13992
          | exact resolve b3e13992 b3e11676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13992
        have b3e14121 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op X0 (M.op (M.op (M.op y X0) (M.op x X2)) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e14016 X0 X1 X2 X3
             have i₂ := b3e10104 X2 (M.op y X0) x X3
             grind)
          | exact superpose b3e10104 b3e14016
          | exact resolve b3e14016 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14016
        have b3e14219 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op X0 (M.op (M.op X0 (M.op y (M.op x X2))) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e14121 X0 X1 X2 X3
             have i₂ := b3e10104 (M.op x X2) X0 y X3
             grind)
          | exact superpose b3e10104 b3e14121
          | exact resolve b3e14121 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14121
        have b3e14304 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op X0 (M.op (M.op X0 (M.op x X2)) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e14219 X0 X1 X2 X3
             have i₂ := b3e9694 (M.op x X2) X0 X3
             grind)
          | exact superpose b3e9694 b3e14219
          | exact resolve b3e14219 b3e9694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14219
        have b3e14366 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op X0 (M.op (M.op X0 (M.op y X2)) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e14304 X0 X1 X2 X3
             have i₂ := b3e13039 X2
             grind)
          | exact superpose b3e13039 b3e14304
          | exact resolve b3e14304 b3e13039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14304
        have b3e14412 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 x)) (M.op X1 X3)) = (M.op X0 (M.op (M.op X0 X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e14366 X0 X1 X2 X3
             have i₂ := b3e9694 X2 X0 X3
             grind)
          | exact superpose b3e9694 b3e14366
          | exact resolve b3e14366 b3e9694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14366
        have b3e14440 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X0 X2) X3)) = (M.op y (M.op (M.op X2 x) X3)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e14412 X0 x X2 X3
             have i₂ := b3e1886 X3 (M.op X2 x) x
             grind)
          | exact superpose b3e1886 b3e14412
          | exact resolve b3e14412 b3e1886
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1886 b3e14412
        have b3e14456 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X0 X2) X3)) = (M.op x (M.op X2 X3)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e14440 X0 X2 X3
             have i₂ := b3e2501 x X2 X3
             grind)
          | exact superpose b3e2501 b3e14440
          | exact resolve b3e14440 b3e2501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2501 b3e14440
        have b3e14465 : ∀ X0 X2 X3 : G, (M.op y (M.op X2 X3)) = (M.op X0 (M.op (M.op X0 X2) X3)) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e14456 X0 X2 X3
             have i₂ := b3e13039 (M.op X2 X3)
             grind)
          | exact superpose b3e13039 b3e14456
          | exact resolve b3e14456 b3e13039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14456
        have b3e16461 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op (M.op X3 X2) (M.op (M.op X0 (M.op (M.op X1 X0) X2)) x)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e89 (M.op X3 X2) (M.op X3 X1)
             have i₂ := b3e32 X2 X0 X1 X3
             grind)
          | exact superpose b3e32 b3e89
          | exact resolve b3e89 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e16715 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op X2 (M.op (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3) x)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e16461 X0 X1 X2 X3
             have i₂ := b3e11676 X2 (M.op X0 (M.op (M.op X1 X0) X2)) X3 x
             grind)
          | exact superpose b3e11676 b3e16461
          | exact resolve b3e16461 b3e11676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11676 b3e16461
        have b3e16864 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op X2 (M.op (M.op (M.op (M.op X1 X0) X2) (M.op X0 X3)) x)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e16715 X0 X1 X2 X3
             have i₂ := b3e10104 X3 (M.op (M.op X1 X0) X2) X0 x
             grind)
          | exact superpose b3e10104 b3e16715
          | exact resolve b3e16715 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16715
        have b3e16978 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op X2 (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 X3))) x)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e16864 X0 X1 X2 X3
             have i₂ := b3e10104 (M.op X0 X3) X2 (M.op X1 X0) x
             grind)
          | exact superpose b3e10104 b3e16864
          | exact resolve b3e16864 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16864
        have b3e17065 : ∀ X0 X1 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op y (M.op (M.op (M.op X1 X0) (M.op X0 X3)) x)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e16978 X0 X1 x X3
             have i₂ := b3e14465 x (M.op (M.op X1 X0) (M.op X0 X3)) x
             grind)
          | (have i₁ := b3e16978 X0 X1 y X3
             have i₂ := b3e14465 X0 (M.op y (M.op (M.op X1 X0) (M.op X0 X3))) x
             grind)
          | exact superpose b3e14465 b3e16978
          | exact resolve b3e16978 b3e14465
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e14465 b3e16978
        have b3e17129 : ∀ X0 X1 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op (M.op (M.op X1 X0) (M.op X0 X3)) y) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17065 X0 X1 X3
             have i₂ := b3e13473 (M.op (M.op X1 X0) (M.op X0 X3))
             grind)
          | exact superpose b3e13473 b3e17065
          | exact resolve b3e17065 b3e13473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17065
        have b3e17185 : ∀ X0 X1 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op (M.op X0 (M.op X1 (M.op X0 X3))) y) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17129 X0 X1 X3
             have i₂ := b3e10104 (M.op X0 X3) X0 X1 y
             grind)
          | exact superpose b3e10104 b3e17129
          | exact resolve b3e17129 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17129
        have b3e17231 : ∀ X0 X1 X3 : G, (M.op (M.op x (M.op X3 X1)) y) = (M.op X0 (M.op (M.op X1 (M.op X0 X3)) x)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17185 X0 X1 X3
             have i₂ := b3e13484 X0 (M.op X1 (M.op X0 X3))
             grind)
          | exact superpose b3e13484 b3e17185
          | exact resolve b3e17185 b3e13484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17185
        have b3e17259 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X3)) x)) = (M.op x (M.op (M.op X3 X1) x)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17231 X0 X1 X3
             have i₂ := b3e13484 x (M.op X3 X1)
             grind)
          | exact superpose b3e13484 b3e17231
          | exact resolve b3e17231 b3e13484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17231
        have b3e17275 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X3)) x)) = (M.op y (M.op (M.op X3 X1) x)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17259 X0 X1 X3
             have i₂ := b3e13039 (M.op (M.op X3 X1) x)
             grind)
          | exact superpose b3e13039 b3e17259
          | exact resolve b3e17259 b3e13039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17259
        have b3e17283 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X3)) x)) = (M.op (M.op X3 X1) y) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17275 X0 X1 X3
             have i₂ := b3e13473 (M.op X3 X1)
             grind)
          | exact superpose b3e13473 b3e17275
          | exact resolve b3e17275 b3e13473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13473 b3e17275
        have b3e17288 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X3)) x)) = (M.op X3 (M.op X1 x)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e17283 X0 X1 X3
             have i₂ := b3e13484 X3 X1
             grind)
          | exact superpose b3e13484 b3e17283
          | exact resolve b3e17283 b3e13484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17283
        have b3e24651 : x = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13040 y
             have i₂ := b3e13684
             grind)
          | exact superpose b3e13684 b3e13040
          | exact resolve b3e13040 b3e13684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13040 b3e13684
        have b3e24701 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e24651
             have r₂ := b3e20
             grind)
          | exact resolve b3e24651 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24651
        have b3e25124 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e24701
             grind)
          | exact superpose b3e24701 b3e13
          | exact resolve b3e13 b3e24701
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24701
        have b3e25141 : x = y := by
          first
          | (have i₁ := b3e25124
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e25124
          | exact resolve b3e25124 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25124
        have b3e25204 : y = (M.op (M.op (M.op (M.op (σ y) x) (M.op x (σ x))) (M.op y (M.op x (σ y)))) x) := by
          first
          | (have i₁ := b3e242 (M.op (σ y) x) (σ x)
             have i₂ := b3e152
             grind)
          | exact superpose b3e152 b3e242
          | exact resolve b3e242 b3e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152 b3e242
        have b3e25219 : y = (M.op (M.op (M.op x (σ x)) (M.op (M.op (σ y) x) (M.op y (M.op x (σ y))))) x) := by
          first
          | (have i₁ := b3e25204
             have i₂ := b3e10104 (M.op y (M.op x (σ y))) (M.op x (σ x)) (M.op (σ y) x) x
             grind)
          | exact superpose b3e10104 b3e25204
          | exact resolve b3e25204 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25204
        have b3e25255 : y = (M.op (M.op (σ x) (M.op x (M.op (M.op (σ y) x) (M.op y (M.op x (σ y)))))) x) := by
          first
          | (have i₁ := b3e25219
             have i₂ := b3e10104 (M.op (M.op (σ y) x) (M.op y (M.op x (σ y)))) (σ x) x x
             grind)
          | exact superpose b3e10104 b3e25219
          | exact resolve b3e25219 b3e10104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10104 b3e25219
        have b3e25290 : y = (M.op (M.op (σ y) (M.op y (M.op (M.op (σ y) y) (M.op y (M.op y (σ y)))))) y) := by
          first
          | (have i₁ := b3e25255
             have i₂ := b3e25141
             grind)
          | exact superpose b3e25141 b3e25255
          | exact resolve b3e25255 b3e25141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25255
        have b3e25321 : y = (M.op (M.op (σ y) (M.op (M.op (σ y) y) (M.op y (M.op y (σ y))))) y) := by
          first
          | (have i₁ := b3e25290
             have i₂ := b3e9694 (M.op (M.op (σ y) y) (M.op y (M.op y (σ y)))) (σ y) y
             grind)
          | exact superpose b3e9694 b3e25290
          | exact resolve b3e25290 b3e9694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9694 b3e25290
        have b3e25346 : y = (M.op (σ y) (M.op (M.op (M.op (σ y) y) (M.op y (M.op y (σ y)))) x)) := by
          first
          | (have i₁ := b3e25321
             have i₂ := b3e13484 (σ y) (M.op (M.op (σ y) y) (M.op y (M.op y (σ y))))
             grind)
          | exact superpose b3e13484 b3e25321
          | exact resolve b3e25321 b3e13484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13484 b3e25321
        have b3e25369 : y = (M.op y (M.op (M.op (M.op (σ y) y) (M.op y (M.op y (σ y)))) x)) := by
          first
          | (have i₁ := b3e25346
             have i₂ := b3e695 (M.op (M.op (M.op (σ y) y) (M.op y (M.op y (σ y)))) x)
             grind)
          | exact superpose b3e695 b3e25346
          | exact resolve b3e25346 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25346
        have b3e25387 : y = (M.op (M.op y (σ y)) (M.op (M.op (σ y) y) x)) := by
          first
          | (have i₁ := b3e25369
             have i₂ := b3e17288 y (M.op (σ y) y) (M.op y (σ y))
             grind)
          | exact superpose b3e17288 b3e25369
          | exact resolve b3e25369 b3e17288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17288 b3e25369
        have b3e25404 : y = (M.op (σ y) (M.op (M.op (σ y) y) x)) := by
          first
          | (have i₁ := b3e25387
             have i₂ := b3e721 (M.op (M.op (σ y) y) x) (σ y)
             grind)
          | exact superpose b3e721 b3e25387
          | exact resolve b3e25387 b3e721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e721 b3e25387
        have b3e25419 : y = (M.op y (M.op (M.op (σ y) y) x)) := by
          first
          | (have i₁ := b3e25404
             have i₂ := b3e695 (M.op (M.op (σ y) y) x)
             grind)
          | exact superpose b3e695 b3e25404
          | exact resolve b3e25404 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e695 b3e25404
        have b3e25432 : y = (M.op (M.op x (σ y)) y) := by
          first
          | (have i₁ := b3e25419
             have i₂ := b3e89 y (σ y)
             grind)
          | exact superpose b3e89 b3e25419
          | exact resolve b3e25419 b3e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89 b3e25419
        have b3e25442 : y = (M.op x y) := by
          first
          | (have i₁ := b3e25432
             have i₂ := b3e10333 y x
             grind)
          | exact superpose b3e10333 b3e25432
          | exact resolve b3e25432 b3e10333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10333 b3e25432
        have b3e25451 : y = (M.op y y) := by
          first
          | (have i₁ := b3e25442
             have i₂ := b3e13039 y
             grind)
          | exact superpose b3e13039 b3e25442
          | exact resolve b3e25442 b3e13039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13039 b3e25442
        have b3e25487 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e121
             have i₂ := b3e25141
             grind)
          | exact superpose b3e25141 b3e121
          | exact resolve b3e121 b3e25141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e121 b3e25141
        have b3e25530 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e25487
             have i₂ := b3e25451
             grind)
          | exact superpose b3e25451 b3e25487
          | exact resolve b3e25487 b3e25451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25451 b3e25487
        have b3e25531 : False := by grind
        exact b3e25531
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19
            | exact resolve b4e19 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e33 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, x = (M.op X0 (M.op (M.op x X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op (σ x) X0) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e33 (M.op y (M.op x X0))
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e33
            | exact resolve b4e33 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : (k y x) = (M.op y x) := by grind
          have b4e45 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b4e46 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e45
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e45
            | exact resolve b4e45 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e47 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e46
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e46
            | exact resolve b4e46 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e46
          have b4e71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e128 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e32
            | exact resolve b4e32 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e206 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e33
            | exact resolve b4e33 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e40
          have b4e280 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
               have i₂ := b4e35 (M.op X1 X2) X1 X2 X0
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e440 : (M.op (M.op x y) y) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e206 (M.op (M.op x y) y)
               have i₂ := b4e36 y
               grind)
            | exact superpose b4e36 b4e206
            | exact resolve b4e206 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e459 : (M.op x y) = (M.op (M.op x y) y) := by
            first
            | (have i₁ := b4e440
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e440
            | exact resolve b4e440 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e440
          have b4e517 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op X0 (M.op y X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 (M.op x y) y X1
               have i₂ := b4e459
               grind)
            | exact superpose b4e459 b4e35
            | exact resolve b4e35 b4e459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e521 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e517 X0 X1
               have i₂ := b4e280 (M.op X0 (M.op y X1)) (M.op x y) X0
               grind)
            | exact superpose b4e280 b4e517
            | exact resolve b4e517 b4e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e517
          have b4e688 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e521 X0 (M.op (M.op x y) y)
               have i₂ := b4e36 y
               grind)
            | exact superpose b4e36 b4e521
            | exact resolve b4e521 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e707 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X3)) (M.op X3 X0)) = (M.op X2 (M.op y X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X3 X1 X2 (M.op X2 (M.op y X0))
               have i₂ := b4e521 X2 X0
               grind)
            | exact superpose b4e521 b4e35
            | exact resolve b4e35 b4e521
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e720 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e688 X0
               have i₂ := b4e459
               grind)
            | exact superpose b4e459 b4e688
            | exact resolve b4e688 b4e459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e459 b4e688
          have b4e761 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          clear b4e71
          have b4e1481 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) = (M.op (M.op X2 X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e280 X3 X2 (M.op (M.op X1 X2) (M.op X1 X0))
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e280
            | exact resolve b4e280 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1524 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e280 X1 x (M.op y X0)
               have i₂ := b4e206 X0
               grind)
            | exact superpose b4e206 b4e280
            | exact resolve b4e280 b4e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1570 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X3 (M.op X3 X0))) (M.op X2 X4)) (M.op X4 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e35 X4 X2 (M.op X3 (M.op X3 X0)) X1
               have i₂ := b4e280 X1 X3 X0
               grind)
            | exact superpose b4e280 b4e35
            | exact resolve b4e35 b4e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1595 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X3 X0)) (M.op y (M.op X0 X1))) = X1 := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e1570 X0 X1 x X3 x
               have i₂ := b4e707 (M.op X0 X1) x (M.op X3 (M.op X3 X0)) x
               grind)
            | exact superpose b4e707 b4e1570
            | exact resolve b4e1570 b4e707
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e707 b4e1570
          have b4e1637 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e1595 X0 X1 x
               have i₂ := b4e280 (M.op y (M.op X0 X1)) x X0
               grind)
            | exact superpose b4e280 b4e1595
            | exact resolve b4e1595 b4e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1595
          have b4e1984 : (σ x) = (M.op (σ x) (M.op y (σ y))) := by
            first
            | (have i₁ := b4e1637 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1637
            | exact resolve b4e1637 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1994 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1637 (M.op X1 y) (M.op X1 X0)
               have i₂ := b4e13 X0 y X1
               grind)
            | exact superpose b4e13 b4e1637
            | exact resolve b4e1637 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2989 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 y X0
               have i₂ := b4e1994 (M.op X0 X1) X0
               grind)
            | exact superpose b4e1994 b4e13
            | exact resolve b4e13 b4e1994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2994 : (σ x) = (M.op y (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e37 y
               have i₂ := b4e1994 (σ y) (σ x)
               grind)
            | exact superpose b4e1994 b4e37
            | exact resolve b4e37 b4e1994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e1994
          have b4e3557 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e206 (M.op X1 (M.op X1 X0))
               have i₂ := b4e2989 X1 X0
               grind)
            | exact superpose b4e2989 b4e206
            | exact resolve b4e206 b4e2989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e206 b4e2989
          have b4e4798 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) X0)) (M.op X0 (M.op (M.op y (σ y)) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 (σ x) (M.op y (σ y)) X1
               have i₂ := b4e1984
               grind)
            | exact superpose b4e1984 b4e35
            | exact resolve b4e35 b4e1984
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1984
          have b4e4826 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op y (σ y)) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e4798 X0 X1
               have i₂ := b4e280 (M.op X0 (M.op (M.op y (σ y)) X1)) (σ x) X0
               grind)
            | exact superpose b4e280 b4e4798
            | exact resolve b4e4798 b4e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e280 b4e4798
          have b4e4844 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ y) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e4826 X0 X1
               have i₂ := b4e1524 (σ y) X1
               grind)
            | exact superpose b4e1524 b4e4826
            | exact resolve b4e4826 b4e1524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1524 b4e4826
          have b4e5643 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e521 X0 (M.op (σ x) (σ y))
               have i₂ := b4e2994
               grind)
            | exact superpose b4e2994 b4e521
            | exact resolve b4e521 b4e2994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e521 b4e2994
          have b4e6107 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X2 X1 X2 (M.op (σ y) X0)
               have i₂ := b4e4844 X2 X0
               grind)
            | exact superpose b4e4844 b4e35
            | exact resolve b4e35 b4e4844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e6143 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e1637 y (M.op (σ y) X0)
               have i₂ := b4e4844 y X0
               grind)
            | exact superpose b4e4844 b4e1637
            | exact resolve b4e1637 b4e4844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1637 b4e4844
          have b4e6179 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (M.op X2 X2) X0) := by
            intro X0 X2
            first
            | (have i₁ := b4e6107 X0 x X2
               have i₂ := b4e1481 X2 x X2 X0
               grind)
            | exact superpose b4e1481 b4e6107
            | exact resolve b4e6107 b4e1481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1481 b4e6107
          have b4e6247 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X2 X2) X0) := by
            intro X0 X2
            first
            | (have i₁ := b4e6179 X0 X2
               have i₂ := b4e6143 X0
               grind)
            | exact superpose b4e6143 b4e6179
            | exact resolve b4e6179 b4e6143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6179
          have b4e6678 : (σ (M.op y x)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e6143 (σ x)
               grind)
            | exact superpose b4e6143 b4e47
            | exact resolve b4e47 b4e6143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e6143
          have b4e451986 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e761 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e761
          have b4e451988 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e451986 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e451986
          have b4e451989 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e451988 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e451988
          have b4e452034 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e128 X0 X0
               have i₂ := b4e451989 (τ X0)
               grind)
            | exact superpose b4e451989 b4e128
            | exact resolve b4e128 b4e451989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e452041 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e452034 X0
               have i₂ := b4e451989 X0
               grind)
            | exact superpose b4e451989 b4e452034
            | exact resolve b4e452034 b4e451989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e451989 b4e452034
          have b4e452829 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
            intro X0
            grind
          have b4e452862 : ∀ X0 X1 : G, (M.op y X1) = (M.op (τ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e6247 X1 (τ X0)
               have i₂ := b4e452041 X0
               grind)
            | exact superpose b4e452041 b4e6247
            | exact resolve b4e6247 b4e452041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e452041
          have b4e453126 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b4e452829 X0
               have i₂ := b4e128 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e128 b4e452829
            | exact resolve b4e452829 b4e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128 b4e452829
          have b4e453245 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
            intro X0
            grind
          clear b4e453126
          have b4e453340 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e453245 X0
               have i₂ := b4e6247 X0 X0
               grind)
            | exact superpose b4e6247 b4e453245
            | exact resolve b4e453245 b4e6247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6247 b4e453245
          have b4e453421 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e453340 X0
               have i₂ := b4e452862 X0 (τ X0)
               grind)
            | exact superpose b4e452862 b4e453340
            | exact resolve b4e453340 b4e452862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e452862 b4e453340
          have b4e454472 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op y X0)
               have i₂ := b4e453421 X0
               grind)
            | exact superpose b4e453421 b4e15
            | exact resolve b4e15 b4e453421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e453421
          have b4e456163 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e454472 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e454472
            | exact resolve b4e454472 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e454472
          have b4e456765 : (σ (M.op x y)) = (M.op y (σ (M.op y x))) := by
            first
            | (have i₁ := b4e456163 (M.op y x)
               have i₂ := b4e720 y
               grind)
            | exact superpose b4e720 b4e456163
            | exact resolve b4e456163 b4e720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e720 b4e456163
          have b4e456913 : (σ (M.op x y)) = (M.op y (M.op y (σ x))) := by
            first
            | (have i₁ := b4e456765
               have i₂ := b4e6678
               grind)
            | exact superpose b4e6678 b4e456765
            | exact resolve b4e456765 b4e6678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6678 b4e456765
          have b4e456974 : (σ (M.op x y)) = (M.op x (M.op x (σ x))) := by
            first
            | (have i₁ := b4e456913
               have i₂ := b4e3557 (σ x) y
               grind)
            | exact superpose b4e3557 b4e456913
            | exact resolve b4e456913 b4e3557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3557 b4e456913
          have b4e457020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e456974
               have i₂ := b4e5643 x
               grind)
            | exact superpose b4e5643 b4e456974
            | exact resolve b4e456974 b4e5643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5643 b4e456974
          have b4e457052 : False := by grind
          exact b4e457052
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 X2) (M.op X3 X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e33 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e33 (M.op y (M.op x X0))
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e33
            | exact resolve b5e33 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : (k y x) = (M.op y x) := by grind
          have b5e47 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b5e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ x)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e110 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e28 X1 X0
               grind)
            | exact superpose b5e28 b5e14
            | exact resolve b5e14 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e134 : ∀ X0 X1 : G, (M.op (M.op x (M.op x X0)) (M.op X0 (M.op (M.op y y) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e34 X0 x (M.op y y) X1
               have i₂ := b5e37
               grind)
            | exact superpose b5e37 b5e34
            | exact resolve b5e34 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e154 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X1 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            grind
          have b5e181 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
               have i₂ := b5e34 (M.op X1 X2) X1 X2 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e196 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op y y) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e134 X0 X1
               have i₂ := b5e181 (M.op X0 (M.op (M.op y y) X1)) x X0
               grind)
            | exact superpose b5e181 b5e134
            | exact resolve b5e134 b5e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134
          have b5e220 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) X0) = (M.op X2 (M.op (M.op X1 X2) (M.op y (M.op x X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36 (M.op y (M.op x X0)) X2 X1 x
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e36
            | exact resolve b5e36 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e234 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X4 (M.op (M.op X1 X4) X2)) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e36 X2 X4 X1 x
               have i₂ := b5e36 X2 X0 X1 x
               grind)
            | exact superpose b5e36 b5e36
            | exact resolve b5e36 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e262 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 x
               have i₂ := b5e36 X2 X0 X1 x
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e263 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X0 X1
            grind
          have b5e276 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 x X1
               have i₂ := b5e36 (M.op X1 X2) x X1 X0
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e298 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) X0) = (M.op X2 (M.op (M.op X1 X2) (M.op x (M.op y X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e220 X0 X1 X2
               have i₂ := b5e38 X0
               grind)
            | exact superpose b5e38 b5e220
            | exact resolve b5e220 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220
          have b5e461 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0
               have i₂ := b5e38 X0
               grind)
            | exact superpose b5e38 b5e33
            | exact resolve b5e33 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e464 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op y X1) (M.op x (M.op y X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op x X0) X1 y
               have i₂ := b5e38 X0
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e471 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b5e464 X0 x
               have i₂ := b5e298 X0 y x
               grind)
            | exact superpose b5e298 b5e464
            | exact resolve b5e464 b5e298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e298 b5e464
          have b5e488 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e47 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e597 : ∀ X0 X1 : G, (M.op (M.op x (M.op x X0)) (M.op X0 (M.op y X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e34 X0 x y X1
               have i₂ := b5e471 (M.op x X0)
               grind)
            | exact superpose b5e471 b5e34
            | exact resolve b5e34 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e471
          have b5e637 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e597 X0 X1
               have i₂ := b5e181 (M.op X0 (M.op y X1)) x X0
               grind)
            | exact superpose b5e181 b5e597
            | exact resolve b5e597 b5e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e597
          have b5e664 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e665 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e664
               have r₂ := b5e23
               grind)
            | exact resolve b5e664 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e664
          have b5e666 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e665
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e665
            | exact resolve b5e665 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e665
          have b5e667 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e666
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e666
            | exact resolve b5e666 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e666
          have b5e767 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e69 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e768 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e767 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e767
          have b5e996 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X2 (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X2 (M.op y X0)) X1 X2
               have i₂ := b5e637 X2 X0
               grind)
            | exact superpose b5e637 b5e13
            | exact resolve b5e13 b5e637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e999 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X3)) (M.op X3 X0)) = (M.op X2 (M.op y X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 X3 X1 X2 (M.op X2 (M.op y X0))
               have i₂ := b5e637 X2 X0
               grind)
            | exact superpose b5e637 b5e34
            | exact resolve b5e34 b5e637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e637
          have b5e1575 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e667
               grind)
            | exact superpose b5e667 b5e20
            | exact resolve b5e20 b5e667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e667
          have b5e2953 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e74 x x
               grind)
            | exact superpose b5e74 b5e24
            | (have j1 := b5e74 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e74 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e74 y x
               grind)
            | exact resolve b5e24 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74
          have b5e3103 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e2953
          have b5e3603 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e181 X1 x (M.op y X0)
               have i₂ := b5e461 X0
               grind)
            | exact superpose b5e461 b5e181
            | exact resolve b5e181 b5e461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e461
          have b5e3668 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X3 (M.op X3 X0))) (M.op X2 X4)) (M.op X4 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X4 X2 (M.op X3 (M.op X3 X0)) X1
               have i₂ := b5e181 X1 X3 X0
               grind)
            | exact superpose b5e181 b5e34
            | exact resolve b5e34 b5e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e3718 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X3 X0)) (M.op y (M.op X0 X1))) = X1 := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e3668 X0 X1 x X3 x
               have i₂ := b5e999 (M.op X0 X1) x (M.op X3 (M.op X3 X0)) x
               grind)
            | exact superpose b5e999 b5e3668
            | exact resolve b5e3668 b5e999
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e999 b5e3668
          have b5e3779 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e3718 X0 X1 x
               have i₂ := b5e181 (M.op y (M.op X0 X1)) x X0
               grind)
            | exact superpose b5e181 b5e3718
            | exact resolve b5e3718 b5e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3718
          have b5e4104 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3779 X1 (M.op y (M.op X1 X0))
               have i₂ := b5e3779 X1 X0
               grind)
            | exact superpose b5e3779 b5e3779
            | exact resolve b5e3779 b5e3779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4176 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op (M.op (M.op y (M.op X1 X0)) X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X2 X3 (M.op y (M.op X1 X0)) X1
               have i₂ := b5e3779 X1 X0
               grind)
            | exact superpose b5e3779 b5e36
            | exact resolve b5e36 b5e3779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3779
          have b5e4222 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op y (M.op X1 X0)) (M.op y X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4176 X0 X1 X2 x
               have i₂ := b5e996 X2 x (M.op y (M.op X1 X0))
               grind)
            | exact superpose b5e996 b5e4176
            | exact resolve b5e4176 b5e996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4176
          have b5e4256 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y (M.op (M.op y (M.op X1 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4222 X0 X1 X2
               have i₂ := b5e4104 X2 (M.op y (M.op X1 X0))
               grind)
            | exact superpose b5e4104 b5e4222
            | exact resolve b5e4222 b5e4104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4222
          have b5e4262 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y (M.op (M.op X1 X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4256 X0 X1 X2
               have i₂ := b5e3603 (M.op X1 X0) X2
               grind)
            | exact superpose b5e3603 b5e4256
            | exact resolve b5e4256 b5e3603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4256
          have b5e6802 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 X0)) X4) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e36 X3 X4 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
               have i₂ := b5e276 X1 X2 X0
               grind)
            | exact superpose b5e276 b5e36
            | exact resolve b5e36 b5e276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e6812 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e181 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
               have i₂ := b5e276 X1 X2 X0
               grind)
            | exact superpose b5e276 b5e181
            | exact resolve b5e181 b5e276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e181
          have b5e6819 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X1 (M.op X2 X0)) (M.op y X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e6802 X0 X1 X2 X3 x
               have i₂ := b5e996 X3 x (M.op X1 (M.op X2 X0))
               grind)
            | exact superpose b5e996 b5e6802
            | exact resolve b5e6802 b5e996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6802
          have b5e6974 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op (M.op X1 (M.op X2 X0)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e6819 X0 X1 X2 X3
               have i₂ := b5e4104 X3 (M.op X1 (M.op X2 X0))
               grind)
            | exact superpose b5e4104 b5e6819
            | exact resolve b5e6819 b5e4104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4104 b5e6819
          have b5e7034 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X2 X0) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e6974 X0 X1 X2 X3
               have i₂ := b5e4262 (M.op X2 X0) X1 X3
               grind)
            | exact superpose b5e4262 b5e6974
            | exact resolve b5e6974 b5e4262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6974
          have b5e16539 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op y y) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e262 X2 X1 (M.op (M.op X1 X2) (M.op (M.op y y) X0))
               have i₂ := b5e196 (M.op X1 X2) X0
               grind)
            | exact superpose b5e196 b5e262
            | exact resolve b5e262 b5e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e196 b5e262
          have b5e16585 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op (M.op (M.op y y) X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16539 X0 X1 X2
               have i₂ := b5e7034 X2 (M.op y y) X1 X0
               grind)
            | exact superpose b5e7034 b5e16539
            | exact resolve b5e16539 b5e7034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7034 b5e16539
          have b5e16716 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op (M.op y (M.op y X1)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16585 X0 X1 X2
               have i₂ := b5e6812 X1 y y X0
               grind)
            | exact superpose b5e6812 b5e16585
            | exact resolve b5e16585 b5e6812
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6812 b5e16585
          have b5e16796 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op (M.op y X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16716 X0 X1 X2
               have i₂ := b5e3603 (M.op y X1) X0
               grind)
            | exact superpose b5e3603 b5e16716
            | exact resolve b5e16716 b5e3603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16716
          have b5e16856 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16796 X0 X1 X2
               have i₂ := b5e3603 X1 X0
               grind)
            | exact superpose b5e3603 b5e16796
            | exact resolve b5e16796 b5e3603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3603 b5e16796
          have b5e20774 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) = (M.op X1 (M.op (M.op (M.op X2 X3) X1) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e234 X1 (M.op X2 X3) X4 (M.op X2 (M.op X3 X0))
               have i₂ := b5e276 X2 X3 X0
               grind)
            | exact superpose b5e276 b5e234
            | exact resolve b5e234 b5e276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e234 b5e276
          have b5e21389 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) = (M.op (M.op X2 X3) (M.op y X4)) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e20774 X0 x X2 X3 X4
               have i₂ := b5e996 X4 x (M.op X2 X3)
               grind)
            | exact superpose b5e996 b5e20774
            | exact resolve b5e20774 b5e996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e996 b5e20774
          have b5e21825 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) = (M.op y (M.op (M.op X2 X3) X4)) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e21389 X0 X2 X3 X4
               have i₂ := b5e16856 X4 (M.op X2 X3) y
               grind)
            | (have i₁ := b5e21389 X0 X2 X3 X4
               have i₂ := b5e16856 X4 y (M.op X2 X3)
               grind)
            | exact superpose b5e16856 b5e21389
            | exact resolve b5e21389 b5e16856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21389
          have b5e22106 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e21825 X0 X2 X3 X4
               have i₂ := b5e4262 X3 X2 X4
               grind)
            | exact superpose b5e4262 b5e21825
            | exact resolve b5e21825 b5e4262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4262 b5e21825
          have b5e22301 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X4)) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e22106 X0 X2 X3 X4
               have i₂ := b5e16856 X4 (M.op X2 (M.op X3 X0)) X0
               grind)
            | (have i₁ := b5e22106 X0 X2 X3 X4
               have i₂ := b5e16856 X4 X0 (M.op X2 (M.op X3 X0))
               grind)
            | exact superpose b5e16856 b5e22106
            | exact resolve b5e22106 b5e16856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22106
          have b5e31072 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e3103
               have i₂ := b5e768 x
               grind)
            | exact superpose b5e768 b5e3103
            | (have j1 := b5e768 (σ x)
               grind)
            | exact resolve b5e3103 b5e768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e768 b5e3103
          have b5e31074 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e31072
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31072
            | exact resolve b5e31072 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31072
          have b5e31075 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e31074
          have b5e31092 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e31075
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31075
            | exact resolve b5e31075 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31075
          have b5e34711 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e263 (M.op X1 (M.op X1 X0)) X1
               have i₂ := b5e154 X1 X0
               grind)
            | exact superpose b5e154 b5e263
            | (have j0 := b5e263 X0 X1
               have j1 := b5e154 X1 X1
               grind)
            | exact resolve b5e263 b5e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e154 b5e263
          have b5e35020 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e34711 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34711
          have b5e35247 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e35020 X0 X1
               have i₂ := b5e16856 X1 (M.op X1 (M.op X1 X0)) X0
               grind)
            | (have i₁ := b5e35020 X0 X1
               have i₂ := b5e16856 X1 X0 (M.op X1 (M.op X1 X0))
               grind)
            | exact superpose b5e16856 b5e35020
            | (have j0 := b5e35020 X0 X1
               grind)
            | exact resolve b5e35020 b5e16856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16856 b5e35020
          have b5e35429 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X1
            first
            | (have i₁ := b5e35247 x X1
               have i₂ := b5e22301 x X1 X1 X1
               grind)
            | exact superpose b5e22301 b5e35247
            | (have j0 := b5e35247 x X1
               grind)
            | exact resolve b5e35247 b5e22301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22301 b5e35247
          have b5e35565 : ∀ X1 : G, (k X1 (M.op X1 X1)) = X1 := by
            intro X1
            first
            | (have j0 := b5e35429 X1
               have j1 := b5e488 X1
               grind)
            | (have r₁ := b5e35429 x
               have r₂ := b5e488 x
               grind)
            | exact resolve b5e35429 b5e488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e488 b5e35429
          have b5e35776 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e110 X0 (M.op (σ X0) (σ X0))
               have i₂ := b5e35565 (σ X0)
               grind)
            | exact superpose b5e35565 b5e110
            | exact resolve b5e110 b5e35565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110 b5e35565
          have b5e35780 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35776 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e35776
            | exact resolve b5e35776 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35776
          have b5e46918 : x = (k x (τ (σ x))) ∨ x = y := by
            first
            | (have i₁ := b5e35780 x
               have i₂ := b5e31092
               grind)
            | exact superpose b5e31092 b5e35780
            | exact resolve b5e35780 b5e31092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31092 b5e35780
          have b5e47055 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e46918
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e46918
            | exact resolve b5e46918 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46918
          have b5e51892 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e69 x x
               have i₂ := b5e47055
               grind)
            | exact superpose b5e47055 b5e69
            | (have j0 := b5e69 x x
               grind)
            | exact resolve b5e69 b5e47055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69 b5e47055
          have b5e51893 : x = (M.op x x) ∨ x = y := by grind
          clear b5e51892
          have b5e51917 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e51893
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e51893
            | exact resolve b5e51893 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51893
          have b5e51918 : x = y := by grind
          clear b5e51917
          have b5e54280 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1575
               have i₂ := b5e51918
               grind)
            | exact superpose b5e51918 b5e1575
            | exact resolve b5e1575 b5e51918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1575 b5e51918
          have b5e54300 : False := by grind
          exact b5e54300
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X0 (M.op X2 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X3 (M.op (M.op X1 X2) (M.op X1 X0)) X2
             have i₂ := b6e12 X0 X2 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ y) X0) (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op (M.op X3 X2) (M.op X3 X0)) X1 X2
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e36 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e50 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e52 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e19
          | exact resolve b6e19 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e86 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b6e27 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e27
          | exact resolve b6e27 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e87 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b6e27 (M.op (σ x) (M.op (σ y) X0))
             have i₂ := b6e27 X0
             grind)
          | exact superpose b6e27 b6e27
          | exact resolve b6e27 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e101 : (M.op (M.op (σ y) (σ y)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e27 (M.op (M.op (σ y) (σ y)) (σ x))
             have i₂ := b6e29 (σ y)
             grind)
          | exact superpose b6e29 b6e27
          | exact resolve b6e27 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e102 : (M.op (M.op (σ y) (σ y)) (σ x)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e101
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e101
          | exact resolve b6e101 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36 b6e101
        have b6e106 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e102
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e102
          | exact resolve b6e102 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e179 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X1 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X2 X0) (M.op X1 (M.op X1 X2)) (M.op X1 X2)
             have i₂ := b6e28 (M.op X1 X2) X1 X2 X0
             grind)
          | exact superpose b6e28 b6e12
          | exact resolve b6e12 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e255 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 X1 x
             have i₂ := b6e30 X2 X0 X1 x
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e269 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 x X1
             have i₂ := b6e30 (M.op X1 X2) x X1 X0
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e308 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X1 (M.op (M.op X0 X1) (M.op (σ x) (σ x)))) := by
          intro X0 X1
          first
          | (have i₁ := b6e30 (M.op (σ x) (σ x)) X1 X0 (σ y)
             have i₂ := b6e86
             grind)
          | exact superpose b6e86 b6e30
          | exact resolve b6e30 b6e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e359 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op (M.op (M.op X1 X0) X3) X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e30 X2 X3 (M.op X1 X0) X1
             have i₂ := b6e179 (M.op X1 X2) X1 X0
             grind)
          | exact superpose b6e179 b6e30
          | exact resolve b6e30 b6e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e361 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (M.op X1 X0) X1
             have i₂ := b6e179 (M.op X1 X2) X1 X0
             grind)
          | exact superpose b6e179 b6e12
          | exact resolve b6e12 b6e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e476 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X1 X2)) (M.op X3 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e255 X2 X1 (M.op (M.op X3 (M.op X1 X2)) (M.op X3 X0))
             have i₂ := b6e12 X0 (M.op X1 X2) X3
             grind)
          | exact superpose b6e12 b6e255
          | exact resolve b6e255 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e688 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X4)) = (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e30 X4 (M.op X2 (M.op X3 X0)) (M.op X2 X3) X1
             have i₂ := b6e269 X2 X3 X0
             grind)
          | exact superpose b6e269 b6e30
          | exact resolve b6e30 b6e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e689 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 X0)) X4) X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e30 X3 X4 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
             have i₂ := b6e269 X1 X2 X0
             grind)
          | exact superpose b6e269 b6e30
          | exact resolve b6e30 b6e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e691 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op X1 X2) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e179 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
             have i₂ := b6e269 X1 X2 X0
             grind)
          | exact superpose b6e269 b6e179
          | exact resolve b6e179 b6e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e179
        have b6e695 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X2 X0) (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e689 X0 X1 X2 X3 x
             have i₂ := b6e359 (M.op X2 X0) X1 X3 x
             grind)
          | exact superpose b6e359 b6e689
          | exact resolve b6e689 b6e359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e359 b6e689
        have b6e696 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X4)) = (M.op X2 (M.op X3 X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b6e688 X0 x X2 X3 X4
             have i₂ := b6e476 X4 X2 X3 x
             grind)
          | exact superpose b6e476 b6e688
          | exact resolve b6e688 b6e476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e688
        have b6e732 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 X2) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b6e696 X0 X2 X3 X4
             have i₂ := b6e695 (M.op X3 X0) X0 X2 X4
             grind)
          | exact superpose b6e695 b6e696
          | exact resolve b6e696 b6e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e696
        have b6e748 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b6e732 X0 X2 X3 X4
             have i₂ := b6e695 X0 (M.op X0 X2) X3 X4
             grind)
          | exact superpose b6e695 b6e732
          | exact resolve b6e732 b6e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e695 b6e732
        have b6e755 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op (M.op X0 (M.op X2 X3)) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b6e748 X0 X2 X3 X4
             have i₂ := b6e691 X3 X0 X2 X4
             grind)
          | exact superpose b6e691 b6e748
          | exact resolve b6e748 b6e691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e691 b6e748
        have b6e783 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e50 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e798 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (M.op (σ y) X0)) (M.op (σ y) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e361 (M.op (σ x) (M.op (σ y) X0)) (σ y) X1
             have i₂ := b6e27 X0
             grind)
          | exact superpose b6e27 b6e361
          | exact resolve b6e361 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e853 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e255 X2 X1 (M.op X2 (M.op X1 X0))
             have i₂ := b6e361 X2 X1 X0
             grind)
          | exact superpose b6e361 b6e255
          | exact resolve b6e255 b6e361
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e863 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X0)) (M.op X0 X4)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e30 X4 (M.op X3 (M.op X2 X0)) (M.op X2 X3) X1
             have i₂ := b6e361 X3 X2 X0
             grind)
          | exact superpose b6e361 b6e30
          | exact resolve b6e30 b6e361
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e361
        have b6e874 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X0)) (M.op X0 X4)) = (M.op X2 (M.op X3 X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b6e863 X0 x X2 X3 X4
             have i₂ := b6e476 X4 X2 X3 x
             grind)
          | exact superpose b6e476 b6e863
          | exact resolve b6e863 b6e476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e476 b6e863
        have b6e918 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e798 X0 X1
             have i₂ := b6e853 X1 (M.op (σ x) (M.op (σ y) X0)) (σ y)
             grind)
          | (have i₁ := b6e798 X0 X1
             have i₂ := b6e853 X1 (σ y) (M.op (σ x) (M.op (σ y) X0))
             grind)
          | exact superpose b6e853 b6e798
          | exact resolve b6e798 b6e853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e798
        have b6e923 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X0 (M.op (M.op X3 (M.op X2 X0)) X4)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b6e874 X0 X2 X3 X4
             have i₂ := b6e853 X4 (M.op X3 (M.op X2 X0)) X0
             grind)
          | (have i₁ := b6e874 X0 X2 X3 X4
             have i₂ := b6e853 X4 X0 (M.op X3 (M.op X2 X0))
             grind)
          | exact superpose b6e853 b6e874
          | exact resolve b6e874 b6e853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e874
        have b6e943 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) X0)) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e918 X0 X1
             have i₂ := b6e87 X0
             grind)
          | exact superpose b6e87 b6e918
          | exact resolve b6e918 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87 b6e918
        have b6e952 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e943 X0 X1
             have i₂ := b6e755 (σ y) (σ x) X0 X1
             grind)
          | (have i₁ := b6e943 X0 x
             have i₂ := b6e755 X0 (σ y) (M.op (σ y) (M.op (σ x) X0)) x
             grind)
          | exact superpose b6e755 b6e943
          | exact resolve b6e943 b6e755
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e755 b6e943
        have b6e1001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (k x y) = (M.op y x) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e67 x y
             grind)
          | exact superpose b6e67 b6e52
          | (have j1 := b6e67 x y
             grind)
          | exact resolve b6e52 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52 b6e67
        have b6e1050 : y = (M.op x x) ∨ (k x y) = (M.op y x) := by grind
        clear b6e1001
        have b6e1067 : (k x y) = (M.op y x) := by
          first
          | (have r₁ := b6e1050
             have r₂ := b6e21
             grind)
          | exact resolve b6e1050 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1050
        have b6e1221 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ x) (M.op X1 X0)) (M.op X0 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e255 (M.op (σ x) (M.op X1 X0)) X1 X2
             have i₂ := b6e952 X1 X0
             grind)
          | exact superpose b6e952 b6e255
          | exact resolve b6e255 b6e952
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e255 b6e952
        have b6e1243 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op (σ x) (M.op X1 X0)) X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e1221 X0 X1 X2
             have i₂ := b6e853 X2 (M.op (σ x) (M.op X1 X0)) X0
             grind)
          | (have i₁ := b6e1221 X0 X1 X2
             have i₂ := b6e853 X2 X0 (M.op (σ x) (M.op X1 X0))
             grind)
          | exact superpose b6e853 b6e1221
          | exact resolve b6e1221 b6e853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e853 b6e1221
        have b6e1272 : ∀ X1 X2 : G, (M.op X1 (M.op X1 (M.op (σ x) X2))) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b6e1243 x X1 X2
             have i₂ := b6e923 x X1 (σ x) X2
             grind)
          | (have i₁ := b6e1243 X2 X1 x
             have i₂ := b6e923 x X2 (M.op (σ x) (M.op X1 X2)) x
             grind)
          | exact superpose b6e923 b6e1243
          | exact resolve b6e1243 b6e923
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e923 b6e1243
        have b6e2433 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e269 X1 X1 (M.op (σ x) X0)
             have i₂ := b6e1272 X1 X0
             grind)
          | exact superpose b6e1272 b6e269
          | exact resolve b6e269 b6e1272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e269 b6e1272
        have b6e7764 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e79 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e79
          | exact resolve b6e79 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e8080 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e7764
        have b6e16235 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e8080
             grind)
          | exact superpose b6e8080 b6e13
          | exact resolve b6e13 b6e8080
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e16249 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e16235
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e16235
          | exact resolve b6e16235 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16235
        have b6e16271 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e74 y y
             have i₂ := b6e16249
             grind)
          | exact superpose b6e16249 b6e74
          | (have j0 := b6e74 y x
             grind)
          | exact resolve b6e74 b6e16249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74 b6e16249
        have b6e16275 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e16271
        have b6e16284 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e16275
             have r₂ := b6e20
             grind)
          | exact resolve b6e16275 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16275
        have b6e16325 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (M.op (M.op (σ y) X0) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ (k x y)) X0 (σ y)
             have i₂ := b6e106
             grind)
          | exact superpose b6e106 b6e12
          | exact resolve b6e12 b6e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e16384 : (M.op (M.op (σ y) (σ y)) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e16325 x
             have i₂ := b6e308 (σ y) x
             grind)
          | exact superpose b6e308 b6e16325
          | exact resolve b6e16325 b6e308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e308 b6e16325
        have b6e16424 : (M.op (M.op (σ y) (σ y)) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e16384
             have i₂ := b6e1067
             grind)
          | exact superpose b6e1067 b6e16384
          | exact resolve b6e16384 b6e1067
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1067 b6e16384
        have b6e16440 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e16424
             have i₂ := b6e2433 (σ y) (σ y)
             grind)
          | exact superpose b6e2433 b6e16424
          | exact resolve b6e16424 b6e2433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2433 b6e16424
        have b6e17769 : y ≠ (M.op y y) ∨ y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e783 y
             have i₂ := b6e16284
             grind)
          | exact superpose b6e16284 b6e783
          | exact resolve b6e783 b6e16284
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e783
        have b6e17803 : y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e17769
             have r₂ := b6e16284
             grind)
          | exact resolve b6e17769 b6e16284
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16284 b6e17769
        have b6e17951 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8080
             have i₂ := b6e17803
             grind)
          | exact superpose b6e17803 b6e8080
          | exact resolve b6e8080 b6e17803
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8080 b6e17803
        have b6e17976 : (σ x) = (σ y) := by grind
        clear b6e17951
        have b6e18027 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e17976
             grind)
          | exact superpose b6e17976 b6e19
          | exact resolve b6e19 b6e17976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e18042 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e16440
             have i₂ := b6e17976
             grind)
          | exact superpose b6e17976 b6e16440
          | exact resolve b6e16440 b6e17976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16440
        have b6e18043 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e17976
             grind)
          | exact superpose b6e17976 b6e13
          | exact resolve b6e13 b6e17976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e18060 : x = y := by
          first
          | (have i₁ := b6e18043
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e18043
          | exact resolve b6e18043 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18043
        have b6e18061 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e18042
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e18042
          | exact resolve b6e18042 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18042
        have b6e18070 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e18027
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e18027
          | exact resolve b6e18027 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18027
        have b6e18075 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e18061
             have i₂ := b6e18060
             grind)
          | exact superpose b6e18060 b6e18061
          | exact resolve b6e18061 b6e18060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18061
        have b6e18083 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e18070
             have i₂ := b6e17976
             grind)
          | exact superpose b6e17976 b6e18070
          | exact resolve b6e18070 b6e17976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17976 b6e18070
        have b6e18093 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e18083
             have i₂ := b6e18060
             grind)
          | exact superpose b6e18060 b6e18083
          | exact resolve b6e18083 b6e18060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18060 b6e18083
        have b6e18097 : False := by grind
        exact b6e18097
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e54 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X1) (σ X0)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e481 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e54 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e3874 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e89 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e89
            | exact resolve b7e89 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e4157 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e3874
          have b7e8435 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e4157
               grind)
            | exact superpose b7e4157 b7e14
            | exact resolve b7e14 b7e4157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e8453 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e8435
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e8435
            | exact resolve b7e8435 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8435
          have b7e9683 : y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e83 x x
               have i₂ := b7e8453
               grind)
            | exact superpose b7e8453 b7e83
            | (have j0 := b7e83 x y
               grind)
            | exact resolve b7e83 b7e8453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e8453
          have b7e9687 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
          clear b7e9683
          have b7e9696 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e9687
               have r₂ := b7e22
               grind)
            | exact resolve b7e9687 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9687
          have b7e10021 : x ≠ (M.op x x) ∨ x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e481 x
               have i₂ := b7e9696
               grind)
            | exact superpose b7e9696 b7e481
            | exact resolve b7e481 b7e9696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e481
          have b7e10043 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e10021
               have r₂ := b7e9696
               grind)
            | exact resolve b7e10021 b7e9696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9696 b7e10021
          have b7e10330 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4157
               have i₂ := b7e10043
               grind)
            | exact superpose b7e10043 b7e4157
            | exact resolve b7e4157 b7e10043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4157 b7e10043
          have b7e10355 : (σ x) = (σ y) := by grind
          clear b7e10330
          have b7e10483 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e10355
               grind)
            | exact superpose b7e10355 b7e23
            | exact resolve b7e23 b7e10355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e10534 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e10483
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e10483
            | exact resolve b7e10483 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10483
          have b7e10546 : False := by grind
          exact b7e10546
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e83 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1031 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e83 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e1032 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e1031
               have r₂ := b8e23
               grind)
            | exact resolve b8e1031 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1031
          have b8e1033 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e1032
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e1032
            | exact resolve b8e1032 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1032
          have b8e1034 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1033
               grind)
            | exact superpose b8e1033 b8e20
            | exact resolve b8e20 b8e1033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1033
          have b8e1211 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e1034
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1034
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e1034 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1034
          have b8e1221 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e1211
          have b8e1228 : x = (M.op y y) := by
            first
            | (have r₁ := b8e1221
               have r₂ := b8e22
               grind)
            | exact resolve b8e1221 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1221
          have b8e1232 : False := by grind
          exact b8e1232
