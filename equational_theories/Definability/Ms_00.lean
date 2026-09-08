import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_x_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e35 : y ≠ y ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e36
      have b0e42 : (M.op x y) = (k x y) := by grind
      clear b0e35
      have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
      have b0e44 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e43
        | exact resolve b0e43 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e43
      have b0e45 : False := by grind
      exact b0e45
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e26
          | exact resolve b1e26 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e31 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e30 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e30
          | exact resolve b1e30 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e34 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e31 (σ x)
             grind)
          | exact superpose b1e31 b1e19
          | exact resolve b1e19 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e36 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have r₁ := b1e15 (σ y) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e36
        have b1e43 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e41
          | exact resolve b1e41 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e52 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e13
          | exact resolve b1e13 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e53 : y = (k y y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e52
          | exact resolve b1e52 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e68 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e69 : y = (M.op y y) := by grind
        clear b1e68
        have b1e80 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e69
             grind)
          | exact superpose b1e69 b1e12
          | exact resolve b1e12 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e83 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e80 X0
             have i₂ := b1e69
             grind)
          | exact superpose b1e69 b1e80
          | exact resolve b1e80 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e84 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e83 X0
             have i₂ := b1e69
             grind)
          | exact superpose b1e69 b1e83
          | exact resolve b1e83 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69 b1e83
        have b1e135 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e34
             have i₂ := b1e84 x
             grind)
          | exact superpose b1e84 b1e34
          | exact resolve b1e34 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e84
        have b1e136 : False := by grind
        exact b1e136
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X0 (M.op X2 (M.op X0 X2))
             have i₂ := b2e12 X0 X2 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y (M.op x y)
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e93 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 x X0 y
             have i₂ := b2e29 x
             grind)
          | exact superpose b2e29 b2e27
          | exact resolve b2e27 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e103 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e93 X0
             grind)
          | exact superpose b2e93 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x X0
             have r₂ := b2e93 X0
             grind)
          | exact resolve b2e15 b2e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e106 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e103 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103
        have b2e646 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e51 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e648 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e646 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e646
        have b2e1929 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e648 x
             have i₂ := b2e106 x
             grind)
          | exact superpose b2e106 b2e648
          | (have j0 := b2e648 x
             grind)
          | exact resolve b2e648 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106 b2e648
        have b2e1943 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e1929
             have i₂ := b2e93 x
             grind)
          | exact superpose b2e93 b2e1929
          | exact resolve b2e1929 b2e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93 b2e1929
        have b2e1944 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1943
        have b2e1967 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 (σ x) X0 (σ x)
             have i₂ := b2e1944
             grind)
          | exact superpose b2e1944 b2e27
          | exact resolve b2e27 b2e1944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e1981 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1967 X0
             have i₂ := b2e1944
             grind)
          | exact superpose b2e1944 b2e1967
          | exact resolve b2e1967 b2e1944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1967
        have b2e1992 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1981 X0
             have i₂ := b2e1944
             grind)
          | exact superpose b2e1944 b2e1981
          | exact resolve b2e1981 b2e1944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1944 b2e1981
        have b2e2235 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1992 (σ y)
             grind)
          | exact superpose b2e1992 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e1992 (σ y)
             grind)
          | exact resolve b2e21 b2e1992
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1992
        have b2e2240 : False := by grind
        exact b2e2240
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e25 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e25
          | exact resolve b3e25 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e31 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e30 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e30
          | exact resolve b3e30 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e35 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e35
        have b3e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b3e46 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e31 y
             grind)
          | exact superpose b3e31 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e31 y
             grind)
          | exact resolve b3e16 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b3e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e115 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e19
          | exact resolve b3e19 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e119 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e31 x
             grind)
          | exact superpose b3e31 b3e115
          | exact resolve b3e115 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e115
        have b3e155 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b3e119
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e119
          | (have j1 := b3e47 x
             grind)
          | exact resolve b3e119 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e119
        have b3e158 : y = (M.op y x) := by grind
        clear b3e155
        have b3e162 : False := by grind
        exact b3e162
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e32 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e37 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e31 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e31
            | exact resolve b4e31 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e38 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e36
            | exact resolve b4e36 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e56 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e38 (σ x)
               grind)
            | exact superpose b4e38 b4e20
            | exact resolve b4e20 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e58 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e56
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e56
            | exact resolve b4e56 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e56
          have b4e59 : False := by grind
          exact b4e59
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e31 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31
            | exact resolve b5e31 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e36 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e41 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e36 X0
               grind)
            | exact superpose b5e36 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | (have r₁ := b5e16 y X0
               have r₂ := b5e36 X0
               grind)
            | exact resolve b5e16 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e42 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e673 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e75 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e675 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e673 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e673
          have b5e1678 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e675 y
               have i₂ := b5e42 y
               grind)
            | exact superpose b5e42 b5e675
            | (have j0 := b5e675 y
               grind)
            | exact resolve b5e675 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e675
          have b5e1692 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have r₁ := b5e1678
               have r₂ := b5e24
               grind)
            | exact resolve b5e1678 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1678
          have b5e1702 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1692
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1692
            | exact resolve b5e1692 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1692
          have b5e1703 : False := by grind
          exact b5e1703
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op (M.op (M.op X2 (M.op X3 X2)) X3) X0) X0)) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 (M.op (M.op X2 (M.op X3 X2)) X3) X0
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X0 (M.op X2 (M.op X0 X2))
             have i₂ := b6e12 X0 X2 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op (M.op X1 (M.op X2 X1)) X2) X0
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op (M.op X1 (M.op X2 X1)) X2) X0
             grind)
          | (have r₁ := b6e15 (M.op (M.op X1 (M.op X2 X1)) X2) X0
             have r₂ := b6e12 X0 X1 X2
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e34 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e33
        have b6e37 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e36
          | exact resolve b6e36 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e50 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ (k x y))) (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ x)
             have i₂ := b6e37
             grind)
          | exact superpose b6e37 b6e12
          | exact resolve b6e12 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 (σ y) X0 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e27
          | exact resolve b6e27 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e79 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ (k x y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e65 X0
             have i₂ := b6e37
             grind)
          | exact superpose b6e37 b6e65
          | exact resolve b6e65 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e80 : ∀ X0 : G, (M.op X0 (M.op (σ (k x y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e25 X0
             have i₂ := b6e37
             grind)
          | exact superpose b6e37 b6e25
          | exact resolve b6e25 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e37
        have b6e325 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op y x)) (σ y))) = X0 ∨ y = (M.op y y) ∨ y = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b6e80 X0
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e80
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e80 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e350 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op y x)) (σ y))) = X0 ∨ y = (M.op y x) := by
          intro X0
          first
          | (have j0 := b6e325 X0
             grind)
          | (have r₁ := b6e325 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e325 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e325
        have b6e352 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op y x)) (σ y))) = X0 := by
          intro X0
          first
          | (have j0 := b6e350 X0
             grind)
          | (have r₁ := b6e350 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e350 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e350
        have b6e581 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ y) (σ (k x y)))) X0) = (k (M.op (σ x) (M.op (σ y) (σ (k x y)))) X0) := by
          intro X0
          first
          | (have i₁ := b6e35 X0 (σ x) (M.op (σ y) (σ (k x y)))
             have i₂ := b6e50 (σ x)
             grind)
          | exact superpose b6e50 b6e35
          | exact resolve b6e35 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e583 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (σ x) (M.op (σ y) (σ (k x y)))) X1) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e26 X1 X0 (σ x) (M.op (σ y) (σ (k x y)))
             have i₂ := b6e50 (σ x)
             grind)
          | exact superpose b6e50 b6e26
          | exact resolve b6e26 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26 b6e50
        have b6e609 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) X1) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e583 X0 X1
             have i₂ := b6e79 (σ x)
             grind)
          | exact superpose b6e79 b6e583
          | exact resolve b6e583 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e583
        have b6e611 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e581 X0
             have i₂ := b6e79 (σ x)
             grind)
          | exact superpose b6e79 b6e581
          | exact resolve b6e581 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e581
        have b6e698 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e611 (σ X0)
             grind)
          | exact superpose b6e611 b6e18
          | exact resolve b6e18 b6e611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e611
        have b6e747 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ (M.op y x)) (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e609 X0 (M.op (σ (M.op y x)) (σ y))
             have i₂ := b6e352 (M.op (σ x) (M.op (σ (M.op y x)) (σ y)))
             grind)
          | exact superpose b6e352 b6e609
          | exact resolve b6e609 b6e352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e609
        have b6e779 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e747 X0
             have i₂ := b6e352 (σ x)
             grind)
          | exact superpose b6e352 b6e747
          | exact resolve b6e747 b6e352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e352 b6e747
        have b6e1153 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e779 (σ x)
             have i₂ := b6e698 x
             grind)
          | exact superpose b6e698 b6e779
          | exact resolve b6e779 b6e698
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e698 b6e779
        have b6e1227 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1153
             grind)
          | exact superpose b6e1153 b6e13
          | exact resolve b6e13 b6e1153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1153
        have b6e1258 : x = (k x x) := by
          first
          | (have i₁ := b6e1227
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1227
          | exact resolve b6e1227 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1227
        have b6e1417 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e1258
             grind)
          | exact superpose b6e1258 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e1258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1258
        have b6e1418 : x = (M.op x x) := by grind
        clear b6e1417
        have b6e1572 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 x X0 x
             have i₂ := b6e1418
             grind)
          | exact superpose b6e1418 b6e27
          | exact resolve b6e27 b6e1418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e1585 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1572 X0
             have i₂ := b6e1418
             grind)
          | exact superpose b6e1418 b6e1572
          | exact resolve b6e1572 b6e1418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1572
        have b6e1594 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1585 X0
             have i₂ := b6e1418
             grind)
          | exact superpose b6e1418 b6e1585
          | exact resolve b6e1585 b6e1418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1418 b6e1585
        have b6e1748 : y ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e1594 y
             grind)
          | exact superpose b6e1594 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e1594 y
             grind)
          | exact resolve b6e20 b6e1594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1594
        have b6e1749 : False := by grind
        exact b6e1749
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have r₁ := b7e16 (σ y) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b7e40
          have b7e46 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e14
            | exact resolve b7e14 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : y = (k y y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e63 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e50
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e50 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e71 : y = (M.op y y) := by grind
          clear b7e63
          have b7e74 : False := by grind
          exact b7e74
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b8e13 X0 X2 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e75 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e93 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e18 X2 X0
               grind)
            | exact superpose b8e18 b8e32
            | (have j1 := b8e18 X2 X0
               grind)
            | exact resolve b8e32 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e97 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 (M.op X1 (M.op X2 (M.op X1 X2))) X0
               have i₂ := b8e32 X1 X0 X2
               grind)
            | exact superpose b8e32 b8e16
            | (have j0 := b8e16 (M.op X1 (M.op X2 (M.op X1 X2))) X0
               grind)
            | (have r₁ := b8e16 (M.op X0 (M.op X2 (M.op X0 X2))) X1
               have r₂ := b8e32 X0 X1 X2
               grind)
            | exact resolve b8e16 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e102 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e97 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e195 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e76 (σ X0)
               grind)
            | exact superpose b8e76 b8e19
            | (have j1 := b8e76 (σ X0)
               grind)
            | exact resolve b8e19 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e688 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e67 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e690 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e688 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e688
          have b8e797 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op (σ X0) (σ (k X0 y))))) = X1 ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 (σ y) X1 (σ X0)
               have i₂ := b8e195 X0
               grind)
            | exact superpose b8e195 b8e32
            | (have j1 := b8e195 X0
               grind)
            | exact resolve b8e32 b8e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e861 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e690 (M.op X0 (M.op X1 (M.op X0 X1)))
               have i₂ := b8e102 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
               grind)
            | exact superpose b8e102 b8e690
            | (have j0 := b8e690 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | exact resolve b8e690 b8e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e690
          have b8e874 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e861 X0 X1
               have i₂ := b8e32 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e32 b8e861
            | (have j0 := b8e861 X0 X1
               grind)
            | exact resolve b8e861 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e861
          have b8e875 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have j0 := b8e874 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e874
          have b8e3078 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X1 X0
               have i₂ := b8e93 X0 X0 X2
               grind)
            | exact superpose b8e93 b8e32
            | (have j1 := b8e93 X0 X1 X2
               grind)
            | exact resolve b8e32 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3081 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e102 X0 X0 X0
               have i₂ := b8e93 X0 X0 X2
               grind)
            | exact superpose b8e93 b8e102
            | (have j1 := b8e93 X0 X1 X2
               grind)
            | exact resolve b8e102 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e4299 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e3078 (σ x) (σ y) X0
               grind)
            | exact superpose b8e3078 b8e23
            | (have j1 := b8e3078 (σ x) x X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e3078 (σ x) (σ y) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e3078 (σ y) x (σ x)
               grind)
            | exact resolve b8e23 b8e3078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3078
          have b8e4304 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e4299 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4299
          have b8e4768 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e4304 (σ X0)
               grind)
            | exact superpose b8e4304 b8e19
            | (have j1 := b8e4304 (σ X0)
               grind)
            | exact resolve b8e19 b8e4304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4304
          have b8e6913 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e4768 y
               grind)
            | exact superpose b8e4768 b8e20
            | (have j1 := b8e4768 y
               grind)
            | exact resolve b8e20 b8e4768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4768
          have b8e18851 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e3081 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3081
          have b8e18852 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e18851 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18851
          have b8e18873 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e18852 X0
               have j1 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e18852 X0
               have r₂ := b8e16 X0 X0
               grind)
            | exact resolve b8e18852 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18852
          have b8e19266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e18873 (σ X0)
               grind)
            | exact superpose b8e18873 b8e19
            | exact resolve b8e19 b8e18873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e19305 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e19266 X0
               have i₂ := b8e18873 X0
               grind)
            | exact superpose b8e18873 b8e19266
            | exact resolve b8e19266 b8e18873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18873 b8e19266
          have b8e20780 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e19305 X0
               grind)
            | exact superpose b8e19305 b8e13
            | exact resolve b8e13 b8e19305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19305
          have b8e27247 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e20780 (M.op X0 (M.op X1 (M.op X0 X1))) X2
               have i₂ := b8e32 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e32 b8e20780
            | exact resolve b8e20780 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20780
          have b8e27741 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e27247 X0 X1 X2
               have i₂ := b8e875 X0 X1
               grind)
            | exact superpose b8e875 b8e27247
            | exact resolve b8e27247 b8e875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27247
          have b8e27789 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e27741 X0 X1 X2
               have i₂ := b8e875 X0 X1
               grind)
            | exact superpose b8e875 b8e27741
            | exact resolve b8e27741 b8e875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e875 b8e27741
          have b8e30026 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e27789 X0 X0 X1
               have i₂ := b8e93 X0 X0 X2
               grind)
            | exact superpose b8e93 b8e27789
            | (have j1 := b8e93 X0 X1 X2
               grind)
            | exact resolve b8e27789 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93 b8e27789
          have b8e256060 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = (k X0 x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e30026 x (σ y) X0
               grind)
            | exact superpose b8e30026 b8e23
            | (have j1 := b8e30026 x x X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e30026 x (σ y) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e30026 (σ y) x (σ x)
               grind)
            | exact resolve b8e23 b8e30026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30026
          have b8e256064 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b8e256060 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256060
          have b8e256099 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e6913
               have i₂ := b8e256064 y
               grind)
            | exact superpose b8e256064 b8e6913
            | (have j1 := b8e256064 y
               grind)
            | exact resolve b8e6913 b8e256064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6913 b8e256064
          have b8e256100 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e256099
          have b8e256113 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 (σ y) (σ x)
               have i₂ := b8e256100
               grind)
            | exact superpose b8e256100 b8e13
            | exact resolve b8e13 b8e256100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256100
          have b8e257940 : ∀ X0 : G, (M.op X0 (M.op (σ (k x y)) (σ x))) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e256113 X0
               have i₂ := b8e195 x
               grind)
            | exact superpose b8e195 b8e256113
            | (have j1 := b8e195 x
               grind)
            | exact resolve b8e256113 b8e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195 b8e256113
          have b8e258069 : ∀ X0 : G, (M.op X0 (M.op (σ (k x y)) (σ x))) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e257940 X0
               grind)
            | (have r₁ := b8e257940 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e257940 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e257940
          have b8e258091 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ (k x y)))) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 (σ x) (σ (k x y))
               have i₂ := b8e258069 (σ x)
               grind)
            | exact superpose b8e258069 b8e13
            | exact resolve b8e13 b8e258069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e258069
          have b8e258690 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e797 x X0
               have i₂ := b8e258091 (σ y)
               grind)
            | exact superpose b8e258091 b8e797
            | (have j0 := b8e797 x x
               grind)
            | exact resolve b8e797 b8e258091
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e797 b8e258091
          have b8e258705 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e258690 X0
               grind)
            | (have r₁ := b8e258690 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e258690 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e258690
          have b8e259015 : (σ y) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e258705 (σ y)
               grind)
            | exact superpose b8e258705 b8e24
            | (have r₁ := b8e24
               have r₂ := b8e258705 (σ y)
               grind)
            | exact resolve b8e24 b8e258705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e258705
          have b8e259048 : x = (M.op x y) := by grind
          clear b8e259015
          have b8e259087 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 x X0 y
               have i₂ := b8e259048
               grind)
            | exact superpose b8e259048 b8e32
            | exact resolve b8e32 b8e259048
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259048
          have b8e259757 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 y X0 x
               have i₂ := b8e259087 y
               grind)
            | exact superpose b8e259087 b8e32
            | exact resolve b8e32 b8e259087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e259087
          have b8e260806 : y ≠ y := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e259757 y
               grind)
            | exact superpose b8e259757 b8e22
            | (have r₁ := b8e22
               have r₂ := b8e259757 y
               grind)
            | exact resolve b8e22 b8e259757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259757
          have b8e260807 : False := by grind
          exact b8e260807

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e28 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e28
        | exact resolve b0e28 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e27 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e27
        | exact resolve b0e27 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e34 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e32
        | exact resolve b0e32 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e35 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e33
        | exact resolve b0e33 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e49 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e34 (σ x)
           grind)
        | exact superpose b0e34 b0e18
        | exact resolve b0e18 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e51 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e49
        | exact resolve b0e49 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e49
      have b0e52 : False := by grind
      exact b0e52
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
        have b1e30 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e25 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e25
          | exact resolve b1e25 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e31 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e30 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e30
          | exact resolve b1e30 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e36 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e31 y
             grind)
          | exact resolve b1e15 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e37 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e36 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e876 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e59 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e877 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e876 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e876
        have b1e1721 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e877 y
             have i₂ := b1e37 y
             grind)
          | exact superpose b1e37 b1e877
          | (have j0 := b1e877 y
             grind)
          | exact resolve b1e877 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e877
        have b1e1736 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b1e1721
             have r₂ := b1e21
             grind)
          | exact resolve b1e1721 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1721
        have b1e1745 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1736
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1736
          | exact resolve b1e1736 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1736
        have b1e1746 : False := by grind
        exact b1e1746
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e25 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
        have b2e29 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e25 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e25
          | exact resolve b2e25 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e30 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op y X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 y
             have i₂ := b2e30 (M.op X0 (M.op y X0))
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e30 y
             grind)
          | exact superpose b2e30 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e30 y
             grind)
          | exact resolve b2e15 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e40 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 y X0
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e16
          | (have j0 := b2e16 y X0
             grind)
          | (have r₁ := b2e16 y X0
             have r₂ := b2e30 X0
             grind)
          | exact resolve b2e16 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e98 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e23 X0 X1
             grind)
          | exact superpose b2e23 b2e13
          | exact resolve b2e13 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e139 : (σ y) ≠ (σ y) ∨ (σ y) = (k y (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e41 (σ y)
             grind)
          | exact superpose b2e41 b2e21
          | (have j1 := b2e41 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e41 (σ y)
             grind)
          | exact resolve b2e21 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e144 : (σ y) = (k y (σ y)) := by grind
        clear b2e139
        have b2e287 : (k (τ y) y) = (τ (σ y)) := by
          first
          | (have i₁ := b2e98 y y
             have i₂ := b2e144
             grind)
          | exact superpose b2e144 b2e98
          | exact resolve b2e98 b2e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98 b2e144
        have b2e291 : y = (k (τ y) y) := by
          first
          | (have i₁ := b2e287
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e287
          | exact resolve b2e287 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e287
        have b2e293 : y = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e291
             have i₂ := b2e36 (τ y)
             grind)
          | exact superpose b2e36 b2e291
          | exact resolve b2e291 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e291
        have b2e338 : ∀ X0 : G, (M.op X0 (M.op (τ y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32 (τ y) X0
             have i₂ := b2e293
             grind)
          | exact superpose b2e293 b2e32
          | exact resolve b2e32 b2e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e293
        have b2e353 : ∀ X0 : G, (M.op X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e338 X0
             have i₂ := b2e30 (τ y)
             grind)
          | exact superpose b2e30 b2e338
          | exact resolve b2e338 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338
        have b2e370 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (k X0 (τ y)) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 (τ y)
             have i₂ := b2e353 (τ y)
             grind)
          | exact superpose b2e353 b2e15
          | (have j0 := b2e15 X0 (τ y)
             grind)
          | (have r₁ := b2e15 X0 (τ y)
             have r₂ := b2e353 (τ y)
             grind)
          | exact resolve b2e15 b2e353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e353
        have b2e388 : ∀ X0 : G, (k X0 (τ y)) = (M.op (τ y) X0) := by
          intro X0
          first
          | (have j0 := b2e370 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e370
        have b2e429 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op (τ y) X0)) := by
          intro X0
          first
          | (have i₁ := b2e24 y X0
             have i₂ := b2e388 X0
             grind)
          | exact superpose b2e388 b2e24
          | exact resolve b2e24 b2e388
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e388
        have b2e434 : ∀ X0 : G, (σ (M.op (τ y) X0)) = (M.op y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e429 X0
             have i₂ := b2e36 (σ X0)
             grind)
          | exact superpose b2e36 b2e429
          | exact resolve b2e429 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e429
        have b2e1177 : (M.op y (σ y)) = (σ (τ y)) := by
          first
          | (have i₁ := b2e434 y
             have i₂ := b2e30 (τ y)
             grind)
          | exact superpose b2e30 b2e434
          | exact resolve b2e434 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e434
        have b2e1197 : y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e1177
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e1177
          | exact resolve b2e1177 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1177
        have b2e1352 : ∀ X0 : G, (M.op X0 (M.op (σ y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32 (σ y) X0
             have i₂ := b2e1197
             grind)
          | exact superpose b2e1197 b2e32
          | exact resolve b2e32 b2e1197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e1197
        have b2e1373 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1352 X0
             have i₂ := b2e30 (σ y)
             grind)
          | exact superpose b2e30 b2e1352
          | exact resolve b2e1352 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e1352
        have b2e1437 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1373 (σ y)
             grind)
          | exact superpose b2e1373 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e1373 (σ y)
             grind)
          | exact resolve b2e21 b2e1373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1373
        have b2e1446 : False := by grind
        exact b2e1446
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e26 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e26
          | exact resolve b3e26 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e31 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e30 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e30
          | exact resolve b3e30 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e31 (σ y)
             grind)
          | exact superpose b3e31 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e31 (σ y)
             grind)
          | exact resolve b3e15 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e70 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e38 (σ X0)
             grind)
          | exact superpose b3e38 b3e18
          | exact resolve b3e18 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e890 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e31 (σ y)
             have i₂ := b3e70 y
             grind)
          | exact superpose b3e70 b3e31
          | exact resolve b3e31 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e70
        have b3e1014 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e890
             grind)
          | exact superpose b3e890 b3e13
          | exact resolve b3e13 b3e890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e890
        have b3e1031 : y = (k y y) := by
          first
          | (have i₁ := b3e1014
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1014
          | exact resolve b3e1014 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1014
        have b3e1133 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e1031
             grind)
          | exact superpose b3e1031 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e1031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1031
        have b3e1134 : y = (M.op y y) := by grind
        clear b3e1133
        have b3e1138 : False := by grind
        exact b3e1138
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b4e13 X0 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y (M.op x y)
               have i₂ := b4e31 y
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e81 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 (σ y) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 x X0 y
               have i₂ := b4e36 x
               grind)
            | exact superpose b4e36 b4e34
            | exact resolve b4e34 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e99 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e91 x
               grind)
            | exact resolve b4e16 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e105 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e99 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e731 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 (σ x) X0 (σ y)
               have i₂ := b4e81 (σ x)
               grind)
            | exact superpose b4e81 b4e34
            | exact resolve b4e34 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e81
          have b4e771 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (σ x)
               have i₂ := b4e731 (σ x)
               grind)
            | exact superpose b4e731 b4e16
            | (have j0 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e16 X0 (σ x)
               have r₂ := b4e731 (σ x)
               grind)
            | exact resolve b4e16 b4e731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e731
          have b4e793 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e771 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e771
          have b4e907 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e793 (σ X0)
               grind)
            | exact superpose b4e793 b4e19
            | exact resolve b4e19 b4e793
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e793
          have b4e911 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e907 X0
               have i₂ := b4e105 X0
               grind)
            | exact superpose b4e105 b4e907
            | exact resolve b4e907 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105 b4e907
          have b4e1471 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e911 y
               grind)
            | exact superpose b4e911 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e911 y
               grind)
            | exact resolve b4e20 b4e911
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e911
          have b4e1489 : False := by grind
          exact b4e1489
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e31 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b5e13 X0 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y (M.op x y)
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e85 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 x X0 y
               have i₂ := b5e35 x
               grind)
            | exact superpose b5e35 b5e33
            | exact resolve b5e33 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e35
          have b5e93 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e85 x
               grind)
            | exact superpose b5e85 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e85 x
               grind)
            | exact resolve b5e16 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 x X0
               have i₂ := b5e85 X0
               grind)
            | exact superpose b5e85 b5e17
            | (have j0 := b5e17 x X0
               grind)
            | (have r₁ := b5e17 x X0
               have r₂ := b5e85 X0
               grind)
            | exact resolve b5e17 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 x
               have i₂ := b5e85 (M.op X0 (M.op x X0))
               grind)
            | exact superpose b5e85 b5e13
            | exact resolve b5e13 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e98 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e95 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e99 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e93 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e568 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e98 X0
               grind)
            | exact superpose b5e98 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e98 X0
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e98 X0
               grind)
            | exact resolve b5e16 b5e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e585 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k x X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e568 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e568
          have b5e1036 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e585 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e585
          have b5e1037 : ∀ X0 : G, (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e1036 X0
               grind)
            | (have r₁ := b5e1036 X0
               have r₂ := b5e85 X0
               grind)
            | exact resolve b5e1036 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1036
          have b5e1076 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e26 X0 x
               have i₂ := b5e1037 (τ X0)
               grind)
            | exact superpose b5e1037 b5e26
            | exact resolve b5e26 b5e1037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e1037
          have b5e1078 : ∀ X0 : G, (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1076 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1076
            | exact resolve b5e1076 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1076
          have b5e1151 : x = (M.op x (σ x)) := by
            first
            | (have i₁ := b5e99 (σ x)
               have i₂ := b5e1078 x
               grind)
            | exact superpose b5e1078 b5e99
            | exact resolve b5e99 b5e1078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99 b5e1078
          have b5e1382 : ∀ X0 : G, (M.op X0 (M.op (σ x) x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e97 (σ x) X0
               have i₂ := b5e1151
               grind)
            | exact superpose b5e1151 b5e97
            | exact resolve b5e97 b5e1151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97 b5e1151
          have b5e1401 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1382 X0
               have i₂ := b5e85 (σ x)
               grind)
            | exact superpose b5e85 b5e1382
            | exact resolve b5e1382 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85 b5e1382
          have b5e1656 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1401 (σ y)
               grind)
            | exact superpose b5e1401 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1401 (σ y)
               grind)
            | exact resolve b5e24 b5e1401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1401
          have b5e1661 : False := by grind
          exact b5e1661
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
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
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e25 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e25
          | exact resolve b6e25 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e30 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e29 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e36 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e30 (σ y)
             grind)
          | exact superpose b6e30 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e30 (σ y)
             grind)
          | exact resolve b6e15 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e36 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e45 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e37 (σ X0)
             grind)
          | exact superpose b6e37 b6e18
          | exact resolve b6e18 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e345 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e30 (σ y)
             have i₂ := b6e45 y
             grind)
          | exact superpose b6e45 b6e30
          | exact resolve b6e30 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30 b6e45
        have b6e397 : (τ (σ y)) = (k y y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e345
             grind)
          | exact superpose b6e345 b6e13
          | exact resolve b6e13 b6e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e345
        have b6e399 : y = (k y y) := by
          first
          | (have i₁ := b6e397
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e397
          | exact resolve b6e397 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e397
        have b6e442 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e399
             grind)
          | exact superpose b6e399 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e399
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e399
        have b6e443 : y = (M.op y y) := by grind
        clear b6e442
        have b6e447 : False := by grind
        exact b6e447
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 (τ X0) X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e25 X0 X1
               grind)
            | exact superpose b7e25 b7e14
            | exact resolve b7e14 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 (M.op X2 (M.op X0 X2))
               have i₂ := b7e13 X0 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e86 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 (σ y) X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e364 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 (σ x) X0 (σ y)
               have i₂ := b7e86 (σ x)
               grind)
            | exact superpose b7e86 b7e33
            | exact resolve b7e33 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e432 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e364 (σ x)
               grind)
            | exact superpose b7e364 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e364 (σ x)
               grind)
            | exact resolve b7e16 b7e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e449 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e432 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e432
          have b7e537 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e30 X0 x
               have i₂ := b7e449 X0
               grind)
            | exact superpose b7e449 b7e30
            | exact resolve b7e30 b7e449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e449
          have b7e971 : (τ (σ x)) = (k (τ (σ x)) x) := by
            first
            | (have i₁ := b7e537 (σ x)
               have i₂ := b7e364 (σ x)
               grind)
            | exact superpose b7e364 b7e537
            | exact resolve b7e537 b7e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e364 b7e537
          have b7e980 : x = (k x x) := by
            first
            | (have i₁ := b7e971
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e971
            | exact resolve b7e971 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e971
          have b7e1058 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e980
               grind)
            | exact superpose b7e980 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e980
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e980
          have b7e1059 : x = (M.op x x) := by grind
          clear b7e1058
          have b7e1200 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 x X0 x
               have i₂ := b7e1059
               grind)
            | exact superpose b7e1059 b7e33
            | exact resolve b7e33 b7e1059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e1210 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1200 X0
               have i₂ := b7e1059
               grind)
            | exact superpose b7e1059 b7e1200
            | exact resolve b7e1200 b7e1059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1200
          have b7e1218 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1210 X0
               have i₂ := b7e1059
               grind)
            | exact superpose b7e1059 b7e1210
            | exact resolve b7e1210 b7e1059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1059 b7e1210
          have b7e1388 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1218 y
               grind)
            | exact superpose b7e1218 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e1218 y
               grind)
            | exact resolve b7e22 b7e1218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1218
          have b7e1389 : False := by grind
          exact b7e1389
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e639 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e67 x y
               grind)
            | exact superpose b8e67 b8e20
            | (have j1 := b8e67 y y
               grind)
            | exact resolve b8e20 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e691 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e639
               have r₂ := b8e23
               grind)
            | exact resolve b8e639 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e639
          have b8e697 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e691
               have r₂ := b8e24
               grind)
            | exact resolve b8e691 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e691
          have b8e700 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e697
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e697
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e697 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e697
          have b8e701 : y = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e700
          have b8e703 : y = (M.op y x) := by
            first
            | (have r₁ := b8e701
               have r₂ := b8e21
               grind)
            | exact resolve b8e701 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e701
          have b8e705 : False := by grind
          exact b8e705

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_y_x_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b0e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e16 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = y := by grind
        have b0e22 : x = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e28 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b0e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X1 (τ X0)
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e18
          | exact resolve b0e18 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
          intro X0 X1
          grind
        have b0e40 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) := by
          intro X0
          grind
        have b0e43 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
          intro X0
          grind
        clear b0e40
        have b0e53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e39 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
             have i₂ := b0e12 X0 (M.op (M.op X0 X1) X0) X1
             grind)
          | exact superpose b0e12 b0e39
          | exact resolve b0e39 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e66 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b0e17 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e13 (k X0 (τ X1))
             have i₂ := b0e30 X1 X0
             grind)
          | exact superpose b0e30 b0e13
          | exact resolve b0e13 b0e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e30
        have b0e85 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e53 y (M.op (M.op X0 x) X0)
             have i₂ := b0e39 X0 x
             grind)
          | exact superpose b0e39 b0e53
          | exact resolve b0e53 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e92 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op y X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1 x
             have i₂ := b0e53 X0 x
             grind)
          | exact superpose b0e53 b0e12
          | exact resolve b0e12 b0e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e53
        have b0e98 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          grind
        clear b0e85
        have b0e227 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b0e66 X0 y
             have i₂ := b0e98 y
             grind)
          | exact superpose b0e98 b0e66
          | (have j0 := b0e66 X0 y
             grind)
          | (have r₁ := b0e66 X0 y
             have r₂ := b0e98 y
             grind)
          | exact resolve b0e66 b0e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e66 b0e98
        have b0e228 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b0e227 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e227
        have b0e632 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        clear b0e80
        have b0e645 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b0e632 X0
             have i₂ := b0e13 X0
             grind)
          | exact superpose b0e13 b0e632
          | (have j0 := b0e632 X0
             grind)
          | exact resolve b0e632 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e632
        have b0e22188 : y = (M.op y (τ (M.op (σ y) (σ y)))) ∨ y = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e228 (τ (M.op (σ y) (σ y)))
             have i₂ := b0e645 y
             grind)
          | exact superpose b0e645 b0e228
          | (have j0 := b0e228 (M.op y (τ (M.op (σ y) (σ y))))
             have j1 := b0e645 y
             grind)
          | exact resolve b0e228 b0e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e228 b0e645
        have b0e22243 : y = (M.op y (τ (M.op (σ y) (σ y)))) ∨ y = (τ (M.op (σ y) (σ y))) := by
          first
          | (have r₁ := b0e22188
             have r₂ := b0e28
             grind)
          | exact resolve b0e22188 b0e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e22188
        have b0e68656 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b0e92 (τ (M.op (σ y) (σ y))) X0
             have i₂ := b0e22243
             grind)
          | exact superpose b0e22243 b0e92
          | exact resolve b0e92 b0e22243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e92 b0e22243
        have b0e68823 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b0e68656 x
             have i₂ := b0e43 x
             grind)
          | exact superpose b0e43 b0e68656
          | exact resolve b0e68656 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43 b0e68656
        have b0e68824 : y = (τ (M.op (σ y) (σ y))) := by grind
        clear b0e68823
        have b0e70192 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e14 (M.op (σ y) (σ y))
             have i₂ := b0e68824
             grind)
          | exact superpose b0e68824 b0e14
          | exact resolve b0e14 b0e68824
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e68824
        have b0e70278 : False := by grind
        exact b0e70278
      · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e17 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : x = y := by grind
          have b1e23 : x ≠ (M.op x y) := by grind
          have b1e24 : x = (M.op (M.op x y) (M.op x y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 (τ X0) X1
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1
            grind
          have b1e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
               have i₂ := b1e13 X0 (M.op (M.op X0 X2) X0) X2
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e35 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
               have i₂ := b1e13 X0 (M.op (M.op X0 X1) X0) X1
               grind)
            | exact superpose b1e13 b1e35
            | exact resolve b1e35 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e57 : ∀ X0 : G, (σ (M.op y y)) ≠ X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            grind
          have b1e63 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            grind
          clear b1e31
          have b1e68 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e63 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e63
            | (have j0 := b1e63 X0
               grind)
            | exact resolve b1e63 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e63
          have b1e71 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e42 y (M.op (M.op X0 x) X0)
               have i₂ := b1e35 X0 x
               grind)
            | exact superpose b1e35 b1e42
            | exact resolve b1e42 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e73 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op y X0) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e42 (M.op X0 X1) X0
               have i₂ := b1e42 X0 X1
               grind)
            | exact superpose b1e42 b1e42
            | exact resolve b1e42 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e76 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e35 X0 x
               have i₂ := b1e42 X0 x
               grind)
            | exact superpose b1e42 b1e35
            | exact resolve b1e35 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e92 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b1e71 X1
               have i₂ := b1e71 X0
               grind)
            | (have i₁ := b1e71 X0
               have i₂ := b1e71 y
               grind)
            | exact superpose b1e71 b1e71
            | exact resolve b1e71 b1e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e95 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            grind
          clear b1e71
          have b1e134 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e42 X1 x
               have i₂ := b1e38 X1 X0 x
               grind)
            | (have i₁ := b1e42 X0 X0
               have i₂ := b1e38 X0 X0 x
               grind)
            | exact superpose b1e38 b1e42
            | exact resolve b1e42 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e135 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X0) X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e35 X1 x
               have i₂ := b1e38 X1 X0 x
               grind)
            | (have i₁ := b1e35 X0 X0
               have i₂ := b1e38 X0 X0 x
               grind)
            | exact superpose b1e38 b1e35
            | exact resolve b1e35 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38
          have b1e579 : ∀ X0 X1 : G, (M.op y (M.op (M.op y (M.op X0 X0)) X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e135 (M.op X0 X0) X1
               have i₂ := b1e134 X0 (M.op X0 X0)
               grind)
            | exact superpose b1e134 b1e135
            | exact resolve b1e135 b1e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e135
          have b1e602 : (k (σ y) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have j0 := b1e57 (σ (M.op y y))
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e57
          have b1e603 : (M.op (σ y) (σ (M.op y y))) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b1e602
               have i₂ := b1e19 y (M.op y y)
               grind)
            | exact superpose b1e19 b1e602
            | exact resolve b1e602 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e602
          have b1e3455 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e68 (σ X0)
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e68
            | exact resolve b1e68 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e68
          have b1e3505 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e3455 X0
               have i₂ := b1e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b1e19 b1e3455
            | (have j0 := b1e3455 X0
               grind)
            | exact resolve b1e3455 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3455
          have b1e5523 : (σ y) = (M.op y (M.op (σ (k y (M.op y y))) (σ y))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b1e35 (σ y) (σ (M.op y y))
               have i₂ := b1e603
               grind)
            | exact superpose b1e603 b1e35
            | exact resolve b1e35 b1e603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35
          have b1e5940 : ∀ X0 : G, (σ y) = (σ (k y (M.op X0 y))) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e3505 y
               have i₂ := b1e92 y x
               grind)
            | (have i₁ := b1e3505 y
               have i₂ := b1e92 X0 y
               grind)
            | exact superpose b1e92 b1e3505
            | exact resolve b1e3505 b1e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e92 b1e3505
          have b1e6002 : ∀ X0 : G, (σ y) = (σ (k y (M.op X0 y))) := by
            intro X0
            first
            | (have j0 := b1e5940 X0
               grind)
            | (have r₁ := b1e5940 X0
               have r₂ := b1e95 X0
               grind)
            | exact resolve b1e5940 b1e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e95 b1e5940
          have b1e51744 : ∀ X0 : G, (M.op y (M.op (M.op (σ (k y (M.op y y))) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (σ (k y (M.op y y))) (σ y)) X0)) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e73 (M.op (σ (k y (M.op y y))) (σ y)) X0
               have i₂ := b1e5523
               grind)
            | exact superpose b1e5523 b1e73
            | exact resolve b1e73 b1e5523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e73 b1e5523
          have b1e51844 : ∀ X0 : G, (M.op y (M.op (M.op (σ y) (σ y)) X0)) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) X0)) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e51744 X0
               have i₂ := b1e6002 y
               grind)
            | exact superpose b1e6002 b1e51744
            | exact resolve b1e51744 b1e6002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e51744
          have b1e51882 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (σ y) (M.op y X0)) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e51844 x
               have i₂ := b1e134 (σ y) x
               grind)
            | exact superpose b1e134 b1e51844
            | exact resolve b1e51844 b1e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e134 b1e51844
          have b1e51892 : ∀ X0 : G, (M.op (σ y) (M.op y X0)) = X0 ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e51882 X0
               have i₂ := b1e76 X0
               grind)
            | exact superpose b1e76 b1e51882
            | exact resolve b1e51882 b1e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e51882
          have b1e51936 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e51892 (M.op y X0)
               have i₂ := b1e76 X0
               grind)
            | exact superpose b1e76 b1e51892
            | exact resolve b1e51892 b1e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e51892
          have b1e52289 : ∀ X0 : G, (M.op y (M.op (M.op y (M.op y (σ y))) X0)) = X0 ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e579 (σ y) X0
               have i₂ := b1e51936 (σ y)
               grind)
            | exact superpose b1e51936 b1e579
            | exact resolve b1e579 b1e51936
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e579
          have b1e52406 : ∀ X0 : G, (M.op y y) = (τ (σ y)) ∨ (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e14 (M.op y y)
               have i₂ := b1e51936 X0
               grind)
            | exact superpose b1e51936 b1e14
            | (have j1 := b1e51936 X0
               grind)
            | exact resolve b1e14 b1e51936
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e51936
          have b1e52506 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e52406 X0
               have i₂ := b1e14 y
               grind)
            | exact superpose b1e14 b1e52406
            | (have j0 := b1e52406 X0
               grind)
            | exact resolve b1e52406 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e52406
          have b1e52524 : ∀ X0 : G, (M.op y (M.op (σ y) X0)) = X0 ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b1e52289 X0
               have i₂ := b1e76 (σ y)
               grind)
            | exact superpose b1e76 b1e52289
            | exact resolve b1e52289 b1e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e76 b1e52289
          have b1e52542 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
            intro X0
            grind
          clear b1e52506
          have b1e52744 : (σ (M.op y y)) ≠ (M.op y (σ y)) := by grind
          clear b1e52542
          have b1e67911 : (σ (M.op y y)) = (M.op y (σ (k y (M.op y y)))) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b1e52524 (σ (M.op y y))
               have i₂ := b1e603
               grind)
            | exact superpose b1e603 b1e52524
            | exact resolve b1e52524 b1e603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e603 b1e52524
          have b1e68060 : (σ (M.op y y)) = (M.op y (σ (k y (M.op y y)))) ∨ (σ y) = (σ (M.op y y)) := by grind
          clear b1e67911
          have b1e68124 : (σ (M.op y y)) = (M.op y (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b1e68060
               have i₂ := b1e6002 y
               grind)
            | exact superpose b1e6002 b1e68060
            | exact resolve b1e68060 b1e6002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e6002 b1e68060
          have b1e68148 : (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b1e68124
               have r₂ := b1e52744
               grind)
            | exact resolve b1e68124 b1e52744
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e52744 b1e68124
          have b1e68636 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b1e14 (M.op y y)
               have i₂ := b1e68148
               grind)
            | exact superpose b1e68148 b1e14
            | exact resolve b1e14 b1e68148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e68148
          have b1e68795 : y = (M.op y y) := by
            first
            | (have i₁ := b1e68636
               have i₂ := b1e14 y
               grind)
            | exact superpose b1e14 b1e68636
            | exact resolve b1e68636 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e68636
          have b1e68821 : False := by grind
          exact b1e68821
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e17 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = y := by grind
          have b2e23 : x ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 (τ X0) X1
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
               have i₂ := b2e13 X0 (M.op (M.op X0 X2) X0) X2
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k (τ X0) X1)
               have i₂ := b2e31 X0 X1
               grind)
            | exact superpose b2e31 b2e14
            | exact resolve b2e14 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e43 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            grind
          have b2e44 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b2e43 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e43
            | (have j0 := b2e43 X0
               grind)
            | exact resolve b2e43 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43
          have b2e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X0 X1
               have i₂ := b2e18 (σ X0) (σ X1)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X0) (σ X1)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e64 : ∀ X0 : G, (σ (M.op y y)) ≠ X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            grind
          have b2e65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e67 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e41 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e41
            | exact resolve b2e41 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e41
          have b2e78 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e36 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e36
            | exact resolve b2e36 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e79 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e36 (M.op X1 X2) X3 X1
               have i₂ := b2e36 X1 X0 X2
               grind)
            | (have i₁ := b2e36 (M.op X1 X1) X1 X0
               have i₂ := b2e36 X0 X1 X2
               grind)
            | exact superpose b2e36 b2e36
            | exact resolve b2e36 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e83 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e36 X1 X3 x
               have i₂ := b2e36 X1 X0 x
               grind)
            | (have i₁ := b2e36 X0 X1 X0
               have i₂ := b2e36 X0 X0 x
               grind)
            | exact superpose b2e36 b2e36
            | exact resolve b2e36 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e88 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e36 X0 x X2
               have i₂ := b2e36 X0 x X1
               grind)
            | (have i₁ := b2e36 X2 X2 X2
               have i₂ := b2e36 X2 X1 X2
               grind)
            | exact superpose b2e36 b2e36
            | exact resolve b2e36 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e90 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 X2 x
               have i₂ := b2e36 X1 X0 x
               grind)
            | (have i₁ := b2e13 X0 X1 X0
               have i₂ := b2e36 X0 X0 X2
               grind)
            | exact superpose b2e36 b2e13
            | exact resolve b2e13 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e91 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X0) X1) (M.op X1 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 (M.op X1 X3) X2 X1
               have i₂ := b2e36 X1 X0 X3
               grind)
            | (have i₁ := b2e13 (M.op X1 X1) X1 X0
               have i₂ := b2e36 X0 X1 X2
               grind)
            | exact superpose b2e36 b2e13
            | exact resolve b2e13 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e92 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X0 x X1
               have i₂ := b2e36 (M.op (M.op X0 X1) X0) x X2
               grind)
            | (have i₁ := b2e13 X0 (M.op (M.op X0 X2) X0) X2
               have i₂ := b2e36 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
               grind)
            | exact superpose b2e36 b2e13
            | exact resolve b2e13 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e197 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e36 X2 (M.op X1 X1) X3
               have i₂ := b2e83 X1 (M.op X1 X1) X0
               grind)
            | (have i₁ := b2e36 X2 (M.op X1 X1) X3
               have i₂ := b2e83 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b2e83 b2e36
            | exact resolve b2e36 b2e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e83
          have b2e412 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) (M.op (M.op X1 X1) X0)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e36 (M.op (M.op X1 X1) X0) x X2
               have i₂ := b2e90 X1 X0 x
               grind)
            | exact superpose b2e90 b2e36
            | exact resolve b2e36 b2e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e90
          have b2e433 : (k (σ y) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have j0 := b2e64 (σ (M.op y y))
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e64
          have b2e434 : (M.op (σ y) (σ (M.op y y))) = (σ (k y (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b2e433
               have i₂ := b2e19 y (M.op y y)
               grind)
            | exact superpose b2e19 b2e433
            | exact resolve b2e433 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e433
          have b2e520 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e19 X1 X2
               have i₂ := b2e58 X0 X2
               grind)
            | exact superpose b2e58 b2e19
            | (have j1 := b2e58 X0 X2
               grind)
            | exact resolve b2e19 b2e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e58
          have b2e598 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e78 X3 X1 x
               have i₂ := b2e78 X0 X1 x
               grind)
            | (have i₁ := b2e78 X0 X1 X3
               have i₂ := b2e78 (M.op X3 X3) X1 X3
               grind)
            | exact superpose b2e78 b2e78
            | exact resolve b2e78 b2e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e36 X2 (M.op X1 X1) X3
               have i₂ := b2e78 X0 X1 X1
               grind)
            | (have i₁ := b2e36 X0 (M.op X1 X1) X2
               have i₂ := b2e78 (M.op X1 X1) X1 X3
               grind)
            | exact superpose b2e78 b2e36
            | exact resolve b2e36 b2e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e78
          have b2e1544 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X1 X2) X1)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e92 X1 X2 (M.op X1 X2)
               have i₂ := b2e36 (M.op X1 X2) X0 X1
               grind)
            | exact superpose b2e36 b2e92
            | exact resolve b2e92 b2e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36
          have b2e1578 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X4) (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b2e92 X2 x X2
               have i₂ := b2e651 X0 X1 X2 x
               grind)
            | (have i₁ := b2e92 X2 (M.op X1 X1) X2
               have i₂ := b2e651 X2 X1 X2 x
               grind)
            | exact superpose b2e651 b2e92
            | exact resolve b2e92 b2e651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e651
          have b2e2007 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X4 X4) (M.op X0 X3)) (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e79 X0 (M.op X0 X2) X0 X3
               have i₂ := b2e88 X0 X1 X2
               grind)
            | (have i₁ := b2e79 X0 (M.op X0 X1) X0 X3
               have i₂ := b2e88 X0 X1 X2
               grind)
            | exact superpose b2e88 b2e79
            | exact resolve b2e79 b2e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e79 b2e88
          have b2e2232 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X4 X4) (M.op X0 X3)) (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b2e2007 X0 X1 x X3 X4
               have i₂ := b2e13 X0 x X1
               grind)
            | exact superpose b2e13 b2e2007
            | exact resolve b2e2007 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2007
          have b2e3696 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e44 (σ X0)
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e44
            | exact resolve b2e44 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44
          have b2e3737 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e3696 X0
               have i₂ := b2e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b2e19 b2e3696
            | (have j0 := b2e3696 X0
               grind)
            | exact resolve b2e3696 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3696
          have b2e7618 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ (k y (M.op y y))) (σ y))) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ y) X0 (σ (M.op y y))
               have i₂ := b2e434
               grind)
            | exact superpose b2e434 b2e13
            | exact resolve b2e13 b2e434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e434
          have b2e10565 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X4 X4) (M.op (M.op (M.op X1 X1) X0) X2)) X0)) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e91 X0 (M.op (M.op (M.op X1 X1) X0) X2) X2 (M.op (M.op X1 X1) X0)
               have i₂ := b2e412 X0 X1 X2
               grind)
            | exact superpose b2e412 b2e91
            | exact resolve b2e91 b2e412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e91 b2e412
          have b2e12810 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 X2) X0) X3)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e1544 X1 (M.op (M.op X0 X2) X0) X3
               have i₂ := b2e92 X0 X2 X3
               grind)
            | exact superpose b2e92 b2e1544
            | exact resolve b2e1544 b2e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e92 b2e1544
          have b2e14978 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) (M.op (M.op X0 X4) X0)) = X0 := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b2e2232 X0 X4 X1 (M.op x x)
               have i₂ := b2e197 x x (M.op X0 X1) X2
               grind)
            | (have i₁ := b2e2232 X0 X1 x (M.op X0 x)
               have i₂ := b2e197 X0 X1 (M.op X0 x) (M.op X0 x)
               grind)
            | exact superpose b2e197 b2e2232
            | exact resolve b2e2232 b2e197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e197 b2e2232
          have b2e25041 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) ∨ (σ X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e520 (τ X0) X1 X2
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e520
            | exact resolve b2e520 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e520
          have b2e25241 : ∀ X0 X1 X2 : G, (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e25041 X0 X1 X2
               have i₂ := b2e31 X0 X1
               grind)
            | exact superpose b2e31 b2e25041
            | (have j0 := b2e25041 X0 X1 X2
               grind)
            | exact resolve b2e25041 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31 b2e25041
          have b2e160885 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b2e7618 X0
               have i₂ := b2e3737 y
               grind)
            | exact superpose b2e3737 b2e7618
            | (have j1 := b2e3737 y
               grind)
            | exact resolve b2e7618 b2e3737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e7618
          have b2e161294 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            grind
          clear b2e160885
          have b2e189443 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e598 X0 (M.op (σ y) (σ y)) x
               have i₂ := b2e161294 (σ y)
               grind)
            | exact superpose b2e161294 b2e598
            | exact resolve b2e598 b2e161294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e598 b2e161294
          have b2e190682 : ∀ X0 X1 : G, (M.op y y) = (τ (σ y)) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (M.op y y)
               have i₂ := b2e189443 X0 X1
               grind)
            | exact superpose b2e189443 b2e14
            | (have j1 := b2e189443 X0 X1
               grind)
            | exact resolve b2e14 b2e189443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e189443
          have b2e190750 : ∀ X0 X1 : G, y = (M.op y y) ∨ (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e190682 X0 X1
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e190682
            | (have j0 := b2e190682 X0 X1
               grind)
            | exact resolve b2e190682 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e190682
          have b2e190765 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            grind
          clear b2e190750
          have b2e191579 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            grind
          have b2e191900 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (σ y)) X2) (M.op X0 (σ y))) (M.op (M.op X1 X3) X1)) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e14978 X0 (σ y) X2 x
               have i₂ := b2e190765 X0 X1
               grind)
            | (have i₁ := b2e14978 X1 (σ y) X2 x
               have i₂ := b2e190765 X0 X1
               grind)
            | exact superpose b2e190765 b2e14978
            | exact resolve b2e14978 b2e190765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e14978
          have b2e192063 : ∀ X0 X3 : G, (σ y) = (M.op (M.op (M.op X0 (σ y)) X3) (M.op X0 (σ y))) := by
            intro X0 X3
            first
            | (have i₁ := b2e1578 X0 x (σ y) x
               have i₂ := b2e190765 (M.op X0 (M.op x x)) x
               grind)
            | (have i₁ := b2e1578 X0 x (σ y) x
               have i₂ := b2e190765 X0 (M.op X0 (M.op x x))
               grind)
            | exact superpose b2e190765 b2e1578
            | exact resolve b2e1578 b2e190765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1578
          have b2e192087 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op (M.op X3 X3) (M.op X0 (σ y))) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e12810 X1 X3 X2 (σ y)
               have i₂ := b2e190765 (M.op (M.op X1 X2) X1) X0
               grind)
            | (have i₁ := b2e12810 X1 X3 X2 (σ y)
               have i₂ := b2e190765 X0 (M.op (M.op X1 X2) X1)
               grind)
            | exact superpose b2e190765 b2e12810
            | exact resolve b2e12810 b2e190765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e12810
          have b2e192095 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X1 X1) (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b2e10565 (σ y) x x X1 x
               have i₂ := b2e190765 (M.op (M.op x x) (M.op (M.op (M.op x x) (σ y)) x)) X0
               grind)
            | (have i₁ := b2e10565 (σ y) x x X1 x
               have i₂ := b2e190765 X0 (M.op (M.op x x) (M.op (M.op (M.op x x) (σ y)) x))
               grind)
            | exact superpose b2e190765 b2e10565
            | exact resolve b2e10565 b2e190765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e10565 b2e190765
          have b2e192164 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (σ y) X1) := by
            intro X1 X2
            first
            | (have i₁ := b2e192087 x X1 X2 x
               have i₂ := b2e192095 x x
               grind)
            | exact superpose b2e192095 b2e192087
            | exact resolve b2e192087 b2e192095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192087 b2e192095
          have b2e192168 : ∀ X1 X3 : G, (M.op (σ y) (M.op (M.op X1 X3) X1)) = X1 := by
            intro X1 X3
            first
            | (have i₁ := b2e191900 x X1 x X3
               have i₂ := b2e192063 x x
               grind)
            | exact superpose b2e192063 b2e191900
            | exact resolve b2e191900 b2e192063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e191900 b2e192063
          have b2e192243 : ∀ X1 : G, (M.op (σ y) (M.op (σ y) X1)) = X1 := by
            intro X1
            first
            | (have i₁ := b2e192168 X1 x
               have i₂ := b2e192164 X1 x
               grind)
            | exact superpose b2e192164 b2e192168
            | exact resolve b2e192168 b2e192164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192164 b2e192168
          have b2e192261 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e25241 X2 (τ X1) (τ X0)
               have i₂ := b2e67 X1 X0
               grind)
            | exact superpose b2e67 b2e25241
            | (have j0 := b2e25241 X2 (τ X1) X2
               grind)
            | exact resolve b2e25241 b2e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e67 b2e25241
          have b2e192295 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e192261 X0 X1 X2
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e192261
            | (have j0 := b2e192261 X0 X1 X2
               grind)
            | exact resolve b2e192261 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192261
          have b2e192298 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e192295 X0 X1 X2
               have i₂ := b2e15 (k X0 X1)
               grind)
            | exact superpose b2e15 b2e192295
            | (have j0 := b2e192295 X0 X1 X2
               grind)
            | exact resolve b2e192295 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192295
          have b2e192299 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (σ (τ X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e192298 X0 X0 X2
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e192298
            | (have j0 := b2e192298 X0 X1 X2
               grind)
            | exact resolve b2e192298 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192298
          have b2e192300 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e192299 X0 X1 X2
               have i₂ := b2e15 X1
               grind)
            | exact superpose b2e15 b2e192299
            | (have j0 := b2e192299 X0 X1 X2
               grind)
            | exact resolve b2e192299 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192299
          have b2e192718 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e192243 (σ y)
               have i₂ := b2e18 (σ y) X0
               grind)
            | (have i₁ := b2e192243 x
               have i₂ := b2e18 X0 (M.op (σ y) x)
               grind)
            | exact superpose b2e18 b2e192243
            | (have j1 := b2e18 (σ y) X0
               grind)
            | exact resolve b2e192243 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e373189 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e192300 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192300
          have b2e395659 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e373189 (σ y) X0
               have i₂ := b2e191579 (σ y)
               grind)
            | exact superpose b2e191579 b2e373189
            | (have j0 := b2e373189 (σ y) X0
               have j1 := b2e191579 (σ y)
               grind)
            | exact resolve b2e373189 b2e191579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e191579 b2e373189
          have b2e395660 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b2e395659 X0
               have j1 := b2e65 X0 (σ y)
               grind)
            | (have r₁ := b2e395659 X0
               have r₂ := b2e65 (σ y) (M.op (σ y) X0)
               grind)
            | (have r₁ := b2e395659 X0
               have r₂ := b2e65 (M.op (σ y) X0) (σ y)
               grind)
            | (have r₁ := b2e395659 (M.op (σ y) (σ y))
               have r₂ := b2e65 X0 (σ y)
               grind)
            | exact resolve b2e395659 b2e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e65 b2e395659
          have b2e395663 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b2e395660 X0
               have j1 := b2e192718 X0
               grind)
            | (have r₁ := b2e395660 X0
               have r₂ := b2e192718 X0
               grind)
            | (have r₁ := b2e395660 X0
               have r₂ := b2e192718 (M.op (σ y) X0)
               grind)
            | exact resolve b2e395660 b2e192718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192718 b2e395660
          have b2e395715 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e19 y X0
               have i₂ := b2e395663 (σ X0)
               grind)
            | exact superpose b2e395663 b2e19
            | (have j1 := b2e395663 (σ X0)
               grind)
            | exact resolve b2e19 b2e395663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e395663
          have b2e396012 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ (k y X0))) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e192243 (σ X0)
               have i₂ := b2e395715 X0
               grind)
            | exact superpose b2e395715 b2e192243
            | (have j1 := b2e395715 X0
               grind)
            | exact resolve b2e192243 b2e395715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e192243 b2e395715
          have b2e396498 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b2e396012 (M.op y y)
               have i₂ := b2e3737 y
               grind)
            | exact superpose b2e3737 b2e396012
            | (have j0 := b2e396012 (M.op y y)
               have j1 := b2e3737 y
               grind)
            | exact resolve b2e396012 b2e3737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e3737 b2e396012
          have b2e396682 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b2e396498
          have b2e396691 : (σ y) = (σ (M.op y y)) := by grind
          clear b2e396682
          have b2e396710 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b2e14 (M.op y y)
               have i₂ := b2e396691
               grind)
            | exact superpose b2e396691 b2e14
            | exact resolve b2e14 b2e396691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e396691
          have b2e396838 : y = (M.op y y) := by
            first
            | (have i₁ := b2e396710
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e396710
            | exact resolve b2e396710 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e396710
          have b2e396840 : False := by grind
          exact b2e396840
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
        · have b3e21 : x = y := by grind
          have b3e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e31 : False := by grind
          exact b3e31
        · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
          · have b4e22 : x = y := by grind
            have b4e23 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e34 : False := by grind
            exact b4e34
          · have b5e22 : x = y := by grind
            have b5e23 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e34 : False := by grind
            exact b5e34
      · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
        · have b6e21 : x = y := by grind
          have b6e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e31 : False := by grind
          exact b6e31
        · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
          · have b7e22 : x = y := by grind
            have b7e23 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e34 : False := by grind
            exact b7e34
          · have b8e22 : x = y := by grind
            have b8e23 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e34 : False := by grind
            exact b8e34
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e21 : x ≠ y := by grind
          have b9e23 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e29 : y = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 y
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e14
            | exact resolve b9e14 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e30 : x = y := by
            first
            | (have i₁ := b9e29
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e29
            | exact resolve b9e29 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e29
          have b9e31 : False := by grind
          exact b9e31
        · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e22 : x ≠ y := by grind
            have b10e24 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 y
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e15
              | exact resolve b10e15 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : x = y := by
              first
              | (have i₁ := b10e30
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e30
              | exact resolve b10e30 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : False := by grind
            exact b10e32
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e22 : x ≠ y := by grind
            have b11e24 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e15
              | exact resolve b11e15 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e31 : x = y := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e30
              | exact resolve b11e30 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : False := by grind
            exact b11e32
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
              intro X0 X1 X2
              grind
            have b12e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b12e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b12e18 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : x ≠ y := by grind
            have b12e23 : y = (M.op x x) := by grind
            have b12e24 : (σ x) ≠ (σ y) := by grind
            have b12e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b12e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e29 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 (τ X0) X1
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e20
              | exact resolve b12e20 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b12e15 (k (τ X0) X1)
                 have i₂ := b12e30 X0 X1
                 grind)
              | exact superpose b12e30 b12e15
              | exact resolve b12e15 b12e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e30
            have b12e40 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 x X1
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e41 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 X1) X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 (σ x) X1
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e43 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b12e14 x X0 y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e45 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
                 have i₂ := b12e14 X0 X2 x
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e46 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
                 have i₂ := b12e14 X0 (M.op (M.op X0 X2) X0) X2
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e47 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b12e43 X0
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e43
              | exact resolve b12e43 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e43
            have b12e48 : x = (M.op y y) := by
              first
              | (have i₁ := b12e47 x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e47
              | exact resolve b12e47 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e73 : y = (k y x) ∨ x = y := by grind
            have b12e78 : y = (k y x) := by
              first
              | (have r₁ := b12e73
                 have r₂ := b12e22
                 grind)
              | exact resolve b12e73 b12e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e73
            have b12e87 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e40 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
                 have i₂ := b12e14 X0 (M.op (M.op X0 X1) X0) X1
                 grind)
              | exact superpose b12e14 b12e40
              | exact resolve b12e40 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e88 : y = (M.op y x) := by
              first
              | (have i₁ := b12e40 y y
                 have i₂ := b12e47 y
                 grind)
              | exact superpose b12e47 b12e40
              | exact resolve b12e40 b12e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e152 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e46 (M.op X1 X2) X3 X1
                 have i₂ := b12e46 X1 X0 X2
                 grind)
              | (have i₁ := b12e46 (M.op X1 X1) X1 X0
                 have i₂ := b12e46 X0 X1 X2
                 grind)
              | exact superpose b12e46 b12e46
              | exact resolve b12e46 b12e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e160 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X2 X2) y) := by
              intro X0 X2
              first
              | (have i₁ := b12e46 y X2 (M.op (M.op X0 x) X0)
                 have i₂ := b12e40 X0 x
                 grind)
              | exact superpose b12e40 b12e46
              | exact resolve b12e46 b12e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e170 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e46 X0 y X1
                 have i₂ := b12e48
                 grind)
              | exact superpose b12e48 b12e46
              | exact resolve b12e46 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e206 : ∀ X0 : G, x = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e160 X0 x
                 have i₂ := b12e47 x
                 grind)
              | exact superpose b12e47 b12e160
              | exact resolve b12e160 b12e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e47 b12e160
            have b12e222 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e46 X0 X1 y
                 have i₂ := b12e206 X0
                 grind)
              | exact superpose b12e206 b12e46
              | exact resolve b12e46 b12e206
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e224 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 := by
              intro X0
              first
              | (have i₁ := b12e40 X0 y
                 have i₂ := b12e206 X0
                 grind)
              | exact superpose b12e206 b12e40
              | exact resolve b12e40 b12e206
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e225 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x X1)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X1 X0 y
                 have i₂ := b12e206 X1
                 grind)
              | exact superpose b12e206 b12e14
              | exact resolve b12e14 b12e206
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e206
            have b12e278 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X0)) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e45 X0 X1 X0
                 have i₂ := b12e19 X0 X1
                 grind)
              | (have i₁ := b12e45 X0 X1 X2
                 have i₂ := b12e19 X0 (M.op X2 X2)
                 grind)
              | exact superpose b12e19 b12e45
              | (have j1 := b12e19 X1 X0
                 grind)
              | exact resolve b12e45 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e283 : ∀ X0 X1 : G, x = (M.op (M.op X0 X0) (M.op X1 x)) := by
              intro X0 X1
              first
              | (have i₁ := b12e45 X0 X1 y
                 have i₂ := b12e48
                 grind)
              | exact superpose b12e48 b12e45
              | exact resolve b12e45 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e45 b12e48
            have b12e315 : ∀ X1 : G, x = (M.op x (M.op X1 x)) := by
              intro X1
              first
              | (have i₁ := b12e283 x X1
                 have i₂ := b12e222 (M.op X1 x) x
                 grind)
              | exact superpose b12e222 b12e283
              | exact resolve b12e283 b12e222
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e283
            have b12e317 : ∀ X0 X1 X3 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op x (M.op X3 X0)) = X0 ∨ X0 = X1 := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e278 X0 X1 x X3
                 have i₂ := b12e222 (M.op X3 X0) x
                 grind)
              | exact superpose b12e222 b12e278
              | (have j0 := b12e278 X0 X1 x X3
                 grind)
              | exact resolve b12e278 b12e222
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e278
            have b12e374 : ∀ X0 : G, (M.op y x) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b12e224 (M.op X0 x)
                 have i₂ := b12e315 X0
                 grind)
              | exact superpose b12e315 b12e224
              | exact resolve b12e224 b12e315
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e224 b12e315
            have b12e381 : ∀ X0 : G, y = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b12e374 X0
                 have i₂ := b12e88
                 grind)
              | exact superpose b12e88 b12e374
              | exact resolve b12e374 b12e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e88 b12e374
            have b12e402 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e46 X0 X1 x
                 have i₂ := b12e381 X0
                 grind)
              | exact superpose b12e381 b12e46
              | exact resolve b12e46 b12e381
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e46 b12e381
            have b12e415 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b12e402 X0 x
                 have i₂ := b12e222 X0 x
                 grind)
              | exact superpose b12e222 b12e402
              | exact resolve b12e402 b12e222
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e402
            have b12e996 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e87 (σ y) (M.op (M.op X0 x) X0)
                 have i₂ := b12e41 X0 x
                 grind)
              | exact superpose b12e41 b12e87
              | exact resolve b12e87 b12e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e41 b12e87
            have b12e1067 : ∀ X0 : G, (M.op x (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e996 X0
                 have i₂ := b12e415 (σ y)
                 grind)
              | exact superpose b12e415 b12e996
              | exact resolve b12e996 b12e415
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e415 b12e996
            have b12e1633 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e222 X0 (σ x)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e222
              | exact resolve b12e222 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e2275 : (σ x) ≠ (M.op x (σ y)) := by
              first
              | (have i₁ := b12e29
                 have i₂ := b12e1067 (σ x)
                 grind)
              | exact superpose b12e1067 b12e29
              | exact resolve b12e29 b12e1067
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29
            have b12e2665 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e2275
                 have i₂ := b12e1067 X0
                 grind)
              | (have i₁ := b12e2275
                 have i₂ := b12e1067 x
                 grind)
              | exact superpose b12e1067 b12e2275
              | exact resolve b12e2275 b12e1067
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1067
            have b12e6948 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op x X0)) = (M.op (M.op (M.op X3 X3) (M.op X0 X2)) (M.op x X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e152 X0 (M.op X0 X1) X0 X3
                 have i₂ := b12e170 X0 X1
                 grind)
              | exact superpose b12e170 b12e152
              | exact resolve b12e152 b12e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e152 b12e170
            have b12e7318 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op x X0)) = (M.op (M.op x (M.op X0 X2)) (M.op x X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e6948 X0 X1 X2 x
                 have i₂ := b12e222 (M.op X0 X2) x
                 grind)
              | exact superpose b12e222 b12e6948
              | exact resolve b12e6948 b12e222
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e222 b12e6948
            have b12e7500 : ∀ X0 X2 : G, (M.op (M.op x (M.op X0 X2)) (M.op x X0)) = X0 := by
              intro X0 X2
              first
              | (have i₁ := b12e7318 X0 x X2
                 have i₂ := b12e225 x X0
                 grind)
              | exact superpose b12e225 b12e7318
              | exact resolve b12e7318 b12e225
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e225 b12e7318
            have b12e9645 : ∀ X0 : G, (σ x) = (M.op x (σ y)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = X0 := by
              intro X0
              first
              | (have i₁ := b12e317 (σ x) X0 (σ x)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e317
              | (have j0 := b12e317 (σ x) X0 x
                 grind)
              | exact resolve b12e317 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e317
            have b12e9734 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = X0 := by
              intro X0
              first
              | (have j0 := b12e9645 X0
                 grind)
              | (have r₁ := b12e9645 X0
                 have r₂ := b12e2275
                 grind)
              | (have r₁ := b12e9645 (M.op x (σ y))
                 have r₂ := b12e2275
                 grind)
              | exact resolve b12e9645 b12e2275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e2275 b12e9645
            have b12e13582 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ (σ x) = X0 := by
              intro X0
              first
              | (have i₁ := b12e38 X0 x
                 have i₂ := b12e9734 X0
                 grind)
              | exact superpose b12e9734 b12e38
              | (have j1 := b12e9734 X0
                 grind)
              | exact resolve b12e38 b12e9734
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e38 b12e9734
            have b12e16272 : (τ (M.op x (σ x))) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b12e13582 (σ y)
                 have i₂ := b12e1633 (σ x)
                 grind)
              | exact superpose b12e1633 b12e13582
              | (have j0 := b12e13582 (σ y)
                 grind)
              | exact resolve b12e13582 b12e1633
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1633 b12e13582
            have b12e16294 : (τ (M.op x (σ x))) = (k (τ (σ y)) x) := by
              first
              | (have r₁ := b12e16272
                 have r₂ := b12e24
                 grind)
              | exact resolve b12e16272 b12e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e16272
            have b12e16307 : (k y x) = (τ (M.op x (σ x))) := by
              first
              | (have i₁ := b12e16294
                 have i₂ := b12e15 y
                 grind)
              | exact superpose b12e15 b12e16294
              | exact resolve b12e16294 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e16294
            have b12e16314 : y = (τ (M.op x (σ x))) := by
              first
              | (have i₁ := b12e16307
                 have i₂ := b12e78
                 grind)
              | exact superpose b12e78 b12e16307
              | exact resolve b12e16307 b12e78
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e78 b12e16307
            have b12e16632 : (σ y) = (M.op x (σ x)) := by
              first
              | (have i₁ := b12e16 (M.op x (σ x))
                 have i₂ := b12e16314
                 grind)
              | exact superpose b12e16314 b12e16
              | exact resolve b12e16 b12e16314
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e16314
            have b12e16804 : ∀ X0 : G, (σ x) = (M.op (M.op x (M.op (σ x) X0)) (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e7500 (σ x) X0
                 have i₂ := b12e16632
                 grind)
              | exact superpose b12e16632 b12e7500
              | exact resolve b12e7500 b12e16632
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e7500 b12e16632
            have b12e16837 : False := by grind
            exact b12e16837
          · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
                intro X0 X1 X2
                grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e27 : x ≠ (M.op x y) := by grind
              have b13e28 : x = (M.op (M.op x y) (M.op x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e37 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 (M.op x y) X1
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e38 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b13e15 x X0 x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e80 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b13e37 x (M.op (M.op X0 x) X0)
                   have i₂ := b13e37 X0 x
                   grind)
                | exact superpose b13e37 b13e37
                | exact resolve b13e37 b13e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e93 : (M.op x x) = (M.op y x) := by
                first
                | (have i₁ := b13e37 (M.op y x) (M.op y x)
                   have i₂ := b13e38 (M.op y x)
                   grind)
                | exact superpose b13e38 b13e37
                | exact resolve b13e37 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e37 b13e38
              have b13e98 : y = (M.op y x) := by
                first
                | (have i₁ := b13e93
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e93
                | exact resolve b13e93 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e93
              have b13e135 : x = (M.op x y) := by
                first
                | (have i₁ := b13e80 y
                   have i₂ := b13e98
                   grind)
                | exact superpose b13e98 b13e80
                | exact resolve b13e80 b13e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e80 b13e98
              have b13e139 : False := by grind
              exact b13e139
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e19 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 (τ X0) X1
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e35 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 x X1
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e36 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 X1) X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (σ x) X1
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e37 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b14e15 x X0 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e39 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
                   have i₂ := b14e15 X0 X2 x
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
                   have i₂ := b14e15 X0 (M.op (M.op X0 X2) X0) X2
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e43 : x = (M.op y (M.op y x)) := by
                first
                | (have i₁ := b14e35 x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e35
                | exact resolve b14e35 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e44 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
                intro X0
                first
                | (have i₁ := b14e35 y (M.op (M.op X0 x) X0)
                   have i₂ := b14e35 X0 x
                   grind)
                | exact superpose b14e35 b14e35
                | exact resolve b14e35 b14e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e45 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e35 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
                   have i₂ := b14e15 X0 (M.op (M.op X0 X1) X0) X1
                   grind)
                | exact superpose b14e15 b14e35
                | exact resolve b14e35 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X0 X1
                   have i₂ := b14e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e58 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b14e64 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e20 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e58 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e58
              have b14e70 : x = (M.op (σ y) (M.op y x)) := by
                first
                | (have i₁ := b14e37 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e37
                | exact resolve b14e37 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e79 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
                intro X0
                grind
              have b14e80 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e31 X0 X1
                   have i₂ := b14e20 (τ X0) X1
                   grind)
                | exact superpose b14e20 b14e31
                | (have j1 := b14e20 (τ X0) X1
                   grind)
                | exact resolve b14e31 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e83 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k (τ X0) X1)
                   have i₂ := b14e31 X0 X1
                   grind)
                | exact superpose b14e31 b14e16
                | exact resolve b14e16 b14e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e84 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b14e79 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e79
                | (have j0 := b14e79 X0
                   grind)
                | exact resolve b14e79 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e79
              have b14e95 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k X0 (τ X1))
                   have i₂ := b14e32 X1 X0
                   grind)
                | exact superpose b14e32 b14e16
                | exact resolve b14e16 b14e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e100 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e45 (M.op X1 X1) (M.op (M.op X0 x) X0)
                   have i₂ := b14e15 X0 X1 x
                   grind)
                | exact superpose b14e15 b14e45
                | exact resolve b14e45 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e101 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b14e45 (M.op X0 X0) (M.op y x)
                   have i₂ := b14e37 X0
                   grind)
                | exact superpose b14e37 b14e45
                | exact resolve b14e45 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37
              have b14e104 : (M.op x (σ y)) = (M.op y (σ y)) := by
                first
                | (have i₁ := b14e45 (σ y) (M.op y x)
                   have i₂ := b14e70
                   grind)
                | exact superpose b14e70 b14e45
                | exact resolve b14e45 b14e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e70
              have b14e105 : ∀ X0 : G, (M.op X0 y) = (M.op y y) := by
                intro X0
                first
                | (have i₁ := b14e45 y (M.op (M.op X0 x) X0)
                   have i₂ := b14e35 X0 x
                   grind)
                | exact superpose b14e35 b14e45
                | exact resolve b14e45 b14e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e106 : (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b14e45 y (M.op y x)
                   have i₂ := b14e43
                   grind)
                | exact superpose b14e43 b14e45
                | exact resolve b14e45 b14e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e43
              have b14e111 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
                intro X0
                first
                | (have i₁ := b14e35 X0 x
                   have i₂ := b14e45 X0 x
                   grind)
                | exact superpose b14e45 b14e35
                | exact resolve b14e35 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e35
              have b14e112 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op y X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 X1 x
                   have i₂ := b14e45 X0 x
                   grind)
                | exact superpose b14e45 b14e15
                | exact resolve b14e15 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e122 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) := by
                intro X0
                first
                | (have i₁ := b14e36 (σ y) (M.op (M.op X0 x) X0)
                   have i₂ := b14e36 X0 x
                   grind)
                | exact superpose b14e36 b14e36
                | exact resolve b14e36 b14e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e130 : ∀ X0 : G, (M.op y (σ y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e45 (σ y) (M.op (M.op X0 x) X0)
                   have i₂ := b14e36 X0 x
                   grind)
                | exact superpose b14e36 b14e45
                | exact resolve b14e45 b14e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e36
              have b14e136 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e105 X0
                   have i₂ := b14e105 X1
                   grind)
                | (have i₁ := b14e105 X0
                   have i₂ := b14e105 y
                   grind)
                | exact superpose b14e105 b14e105
                | exact resolve b14e105 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e147 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ y = (M.op X0 y) := by
                intro X0
                grind
              have b14e148 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) (M.op (M.op X1 X2) X1)) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 y X2
                   have i₂ := b14e105 X0
                   grind)
                | (have i₁ := b14e15 X0 y X2
                   have i₂ := b14e105 y
                   grind)
                | exact superpose b14e105 b14e15
                | exact resolve b14e15 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e154 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op y X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e148 X0 X1 x
                   have i₂ := b14e45 X1 x
                   grind)
                | exact superpose b14e45 b14e148
                | exact resolve b14e148 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e148
              have b14e184 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op X0 y) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e40 X1 y X2
                   have i₂ := b14e105 X0
                   grind)
                | (have i₁ := b14e40 X0 y X2
                   have i₂ := b14e105 y
                   grind)
                | exact superpose b14e105 b14e40
                | exact resolve b14e40 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e194 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X0) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e45 X1 x
                   have i₂ := b14e40 X1 X0 x
                   grind)
                | (have i₁ := b14e45 X0 X0
                   have i₂ := b14e40 X0 X0 x
                   grind)
                | exact superpose b14e40 b14e45
                | exact resolve b14e45 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40
              have b14e222 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e184 X0 X1 x
                   have i₂ := b14e45 X1 x
                   grind)
                | exact superpose b14e45 b14e184
                | exact resolve b14e184 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e184
              have b14e297 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X2) X0) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e39 (M.op X1 X1) X2 X1
                   have i₂ := b14e20 (M.op X1 X1) X0
                   grind)
                | (have i₁ := b14e39 X0 X1 X2
                   have i₂ := b14e20 X0 (M.op X0 (M.op X2 X2))
                   grind)
                | exact superpose b14e20 b14e39
                | (have j1 := b14e20 (M.op X1 X1) X0
                   grind)
                | exact resolve b14e39 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39
              have b14e334 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op y X0) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e297 X0 X1 x
                   have i₂ := b14e194 x X0
                   grind)
                | exact superpose b14e194 b14e297
                | (have j0 := b14e297 X0 X1 x
                   grind)
                | exact resolve b14e297 b14e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e297
              have b14e343 : ∀ X0 X1 : G, (M.op y X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op y X0) ∨ (M.op X1 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e334 X0 X1
                   have i₂ := b14e194 X1 X0
                   grind)
                | exact superpose b14e194 b14e334
                | (have j0 := b14e334 X0 X1
                   grind)
                | exact resolve b14e334 b14e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e334
              have b14e451 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (M.op y X1) = (k y X1) ∨ y = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e64 X1 y
                   have i₂ := b14e105 X0
                   grind)
                | (have i₁ := b14e64 X0 y
                   have i₂ := b14e105 y
                   grind)
                | exact superpose b14e105 b14e64
                | (have j0 := b14e64 X1 y
                   grind)
                | exact resolve b14e64 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e473 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b14e65 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e65
              have b14e831 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (σ X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e21 X1 X2
                   have i₂ := b14e56 X0 X2
                   grind)
                | exact superpose b14e56 b14e21
                | (have j1 := b14e56 X0 X2
                   grind)
                | exact resolve b14e21 b14e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e56
              have b14e1034 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e83 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e83
                | exact resolve b14e83 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e83
              have b14e1135 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b14e1148 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e1135 X0
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e1135
                | (have j0 := b14e1135 X0
                   grind)
                | exact resolve b14e1135 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1135
              have b14e1151 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e130 X1
                   have i₂ := b14e130 X0
                   grind)
                | (have i₁ := b14e130 X0
                   have i₂ := b14e130 y
                   grind)
                | exact superpose b14e130 b14e130
                | exact resolve b14e130 b14e130
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e130
              have b14e1319 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) (M.op y X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e112 X1 (M.op X0 X0)
                   have i₂ := b14e194 X0 (M.op X0 X0)
                   grind)
                | exact superpose b14e194 b14e112
                | exact resolve b14e112 b14e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e112 b14e194
              have b14e1339 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X0)) (M.op y X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e1319 X0 X1
                   have i₂ := b14e101 X0
                   grind)
                | exact superpose b14e101 b14e1319
                | exact resolve b14e1319 b14e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e101 b14e1319
              have b14e1781 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (M.op X0 (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e45 (M.op X1 y) (M.op y X0)
                   have i₂ := b14e154 X1 X0
                   grind)
                | exact superpose b14e154 b14e45
                | exact resolve b14e45 b14e154
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45 b14e154
              have b14e1785 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e1781 X0 X1
                   have i₂ := b14e44 X1
                   grind)
                | exact superpose b14e44 b14e1781
                | exact resolve b14e1781 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44 b14e1781
              have b14e2042 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) (M.op X0 (σ y))) := by
                intro X0
                first
                | (have i₁ := b14e473 (σ y) (M.op X0 (σ y))
                   have i₂ := b14e122 X0
                   grind)
                | exact superpose b14e122 b14e473
                | (have j0 := b14e473 (σ y) (M.op X0 (σ y))
                   grind)
                | (have r₁ := b14e473 (σ y) (M.op X0 (σ y))
                   have r₂ := b14e122 X0
                   grind)
                | exact resolve b14e473 b14e122
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e122 b14e473
              have b14e2066 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have j0 := b14e2042 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2042
              have b14e2492 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e22
                   have i₂ := b14e1151 (σ x) X0
                   grind)
                | (have i₁ := b14e22
                   have i₂ := b14e1151 X0 (σ x)
                   grind)
                | exact superpose b14e1151 b14e22
                | exact resolve b14e22 b14e1151
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e3049 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e2492 X1
                   have i₂ := b14e136 x X0
                   grind)
                | (have i₁ := b14e2492 X1
                   have i₂ := b14e136 X0 x
                   grind)
                | exact superpose b14e136 b14e2492
                | exact resolve b14e2492 b14e136
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2492
              have b14e4759 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e84 X0
                   have i₂ := b14e80 X0 X1
                   grind)
                | (have i₁ := b14e84 X0
                   have i₂ := b14e80 X0 (M.op (τ X0) (τ X0))
                   grind)
                | exact superpose b14e80 b14e84
                | (have j1 := b14e80 X1 X0
                   grind)
                | exact resolve b14e84 b14e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e80 b14e84
              have b14e4796 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e4759 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e4759
              have b14e5341 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = (M.op y X0) ∨ y = X0 := by
                intro X0
                first
                | (have i₁ := b14e343 X0 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e343
                | exact resolve b14e343 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e5343 : ∀ X0 X1 : G, (M.op y X1) = (k (M.op X0 y) X1) ∨ (M.op X0 y) = (M.op y X1) ∨ (M.op X0 y) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e343 X0 y
                   have i₂ := b14e105 y
                   grind)
                | (have i₁ := b14e343 X0 y
                   have i₂ := b14e105 X0
                   grind)
                | exact superpose b14e105 b14e343
                | exact resolve b14e343 b14e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e105 b14e343
              have b14e5463 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e100 X0 X1
                   have i₂ := b14e100 X2 X1
                   grind)
                | (have i₁ := b14e100 X0 X1
                   have i₂ := b14e100 y X1
                   grind)
                | exact superpose b14e100 b14e100
                | exact resolve b14e100 b14e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e100
              have b14e8613 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op y X2)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e1339 X1 X2
                   have i₂ := b14e5463 x X1 X0
                   grind)
                | (have i₁ := b14e1339 X1 X2
                   have i₂ := b14e5463 X0 X1 x
                   grind)
                | exact superpose b14e5463 b14e1339
                | exact resolve b14e1339 b14e5463
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1339 b14e5463
              have b14e15245 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) ∨ (σ X1) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e831 (τ X0) X1 X2
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e831
                | exact resolve b14e831 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e831
              have b14e15392 : ∀ X0 X1 X2 : G, (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15245 X0 X1 X2
                   have i₂ := b14e31 X0 X1
                   grind)
                | exact superpose b14e31 b14e15245
                | (have j0 := b14e15245 X0 X1 X2
                   grind)
                | exact resolve b14e15245 b14e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31 b14e15245
              have b14e29779 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 (σ y)))) ∨ (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e95 y (M.op X0 (σ y))
                   have i₂ := b14e2066 X0
                   grind)
                | exact superpose b14e2066 b14e95
                | (have j1 := b14e2066 X0
                   grind)
                | exact resolve b14e95 b14e2066
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e95 b14e2066
              have b14e29842 : ∀ X0 : G, y = (k y (τ (M.op X0 (σ y)))) ∨ (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e29779 X0
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e29779
                | (have j0 := b14e29779 X0
                   grind)
                | exact resolve b14e29779 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29779
              have b14e33748 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have i₁ := b14e1148 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e1148
                | exact resolve b14e1148 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1148
              have b14e33921 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have i₁ := b14e33748 X0
                   have i₂ := b14e1034 (M.op X0 X0) X0
                   grind)
                | exact superpose b14e1034 b14e33748
                | (have j0 := b14e33748 X0
                   grind)
                | exact resolve b14e33748 b14e1034
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e33748
              have b14e34066 : ∀ X0 : G, (τ (M.op X0 y)) = (τ (k (M.op X0 y) y)) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e33921 (M.op x y)
                   have i₂ := b14e1785 (M.op x y) x
                   grind)
                | exact superpose b14e1785 b14e33921
                | exact resolve b14e33921 b14e1785
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1785 b14e33921
              have b14e50674 : ∀ X0 X1 : G, (k X1 (σ y)) = (σ (M.op X0 y)) ∨ (k X1 (σ y)) = X1 ∨ y = (τ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e4796 y X1
                   have i₂ := b14e136 (τ X1) X0
                   grind)
                | (have i₁ := b14e4796 y X1
                   have i₂ := b14e136 X0 (τ X1)
                   grind)
                | exact superpose b14e136 b14e4796
                | (have j0 := b14e4796 y X1
                   grind)
                | exact resolve b14e4796 b14e136
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e4796
              have b14e102699 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15392 X2 (τ X1) (τ X0)
                   have i₂ := b14e1034 X1 X0
                   grind)
                | exact superpose b14e1034 b14e15392
                | (have j0 := b14e15392 X2 (τ X1) X2
                   grind)
                | exact resolve b14e15392 b14e1034
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1034 b14e15392
              have b14e103741 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (σ (τ (k X0 X1))) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e102699 X0 X1 X2
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e102699
                | (have j0 := b14e102699 X0 X1 X2
                   grind)
                | exact resolve b14e102699 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e102699
              have b14e103877 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) ∨ (σ (τ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e103741 X0 X1 X2
                   have i₂ := b14e17 (k X0 X1)
                   grind)
                | exact superpose b14e17 b14e103741
                | (have j0 := b14e103741 X0 X1 X2
                   grind)
                | exact resolve b14e103741 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e103741
              have b14e103932 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (σ (τ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e103877 X0 X0 X2
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e103877
                | (have j0 := b14e103877 X0 X1 X2
                   grind)
                | exact resolve b14e103877 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e103877
              have b14e103954 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 X1) = (M.op X2 X1) ∨ X1 = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e103932 X0 X1 X2
                   have i₂ := b14e17 X1
                   grind)
                | exact superpose b14e17 b14e103932
                | (have j0 := b14e103932 X0 X1 X2
                   grind)
                | exact resolve b14e103932 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e103932
              have b14e738622 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e103954 X0 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e103954
              have b14e874289 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 := by
                intro X0 X1
                grind
              have b14e874290 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) ∨ y = X0 ∨ y = (M.op y y) := by
                intro X0
                first
                | (have i₁ := b14e738622 y X0
                   have i₂ := b14e147 y
                   grind)
                | exact superpose b14e147 b14e738622
                | (have j0 := b14e738622 y X0
                   have j1 := b14e147 y
                   grind)
                | exact resolve b14e738622 b14e147
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e147 b14e738622
              have b14e874291 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 ∨ y = (M.op y y) := by
                intro X0
                first
                | (have j0 := b14e874290 X0
                   have j1 := b14e5341 X0
                   grind)
                | (have r₁ := b14e874290 X0
                   have r₂ := b14e5341 X0
                   grind)
                | (have r₁ := b14e874290 X0
                   have r₂ := b14e5341 (M.op y X0)
                   grind)
                | exact resolve b14e874290 b14e5341
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e5341 b14e874290
              have b14e874292 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e874289 X0 X1
                   have j1 := b14e64 X1 X0
                   grind)
                | (have r₁ := b14e874289 X1 X1
                   have r₂ := b14e64 (M.op X1 X1) X1
                   grind)
                | (have r₁ := b14e874289 X0 X1
                   have r₂ := b14e64 X0 (M.op X0 X1)
                   grind)
                | (have r₁ := b14e874289 (M.op X1 X1) X1
                   have r₂ := b14e64 X0 X1
                   grind)
                | exact resolve b14e874289 b14e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64 b14e874289
              have b14e874304 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
                intro X0
                first
                | (have j0 := b14e874291 X0
                   have j1 := b14e451 X0 X0
                   grind)
                | (have r₁ := b14e874291 (M.op X0 y)
                   have r₂ := b14e451 X0 x
                   grind)
                | (have r₁ := b14e874291 X0
                   have r₂ := b14e451 y x
                   grind)
                | exact resolve b14e874291 b14e451
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e451 b14e874291
              have b14e874503 : ∀ X0 : G, (M.op y (σ y)) = (σ (M.op X0 y)) ∨ y = (M.op y (σ y)) ∨ y = (τ y) ∨ y = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e50674 X0 y
                   have i₂ := b14e874304 (σ y)
                   grind)
                | exact superpose b14e874304 b14e50674
                | (have j0 := b14e50674 X0 y
                   have j1 := b14e874304 (M.op y (σ y))
                   grind)
                | exact resolve b14e50674 b14e874304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e50674
              have b14e874624 : y = (M.op y (σ y)) ∨ y = (τ y) ∨ y = (σ y) := by
                first
                | (have r₁ := b14e874503 x
                   have r₂ := b14e3049 x y
                   grind)
                | exact resolve b14e874503 b14e3049
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e874503
              have b14e874635 : y = (M.op x (σ y)) ∨ y = (τ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b14e874624
                   have i₂ := b14e104
                   grind)
                | exact superpose b14e104 b14e874624
                | exact resolve b14e874624 b14e104
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e104 b14e874624
              have b14e875159 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ y = (τ y) ∨ y = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e1151 X0 x
                   have i₂ := b14e874635
                   grind)
                | exact superpose b14e874635 b14e1151
                | exact resolve b14e1151 b14e874635
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1151
              have b14e875168 : y = (k y (τ y)) ∨ y = (σ y) ∨ y = (τ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b14e29842 x
                   have i₂ := b14e874635
                   grind)
                | exact superpose b14e874635 b14e29842
                | exact resolve b14e29842 b14e874635
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e874635
              have b14e875189 : y = (k y (τ y)) ∨ y = (σ y) ∨ y = (τ y) := by grind
              clear b14e875168
              have b14e876737 : y = (M.op y (τ y)) ∨ y = (τ y) ∨ y = (σ y) ∨ y = (τ y) := by
                first
                | (have i₁ := b14e874304 (τ y)
                   have i₂ := b14e875189
                   grind)
                | exact superpose b14e875189 b14e874304
                | (have j0 := b14e874304 (M.op y (τ y))
                   grind)
                | exact resolve b14e874304 b14e875189
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e875189
              have b14e876743 : y = (M.op y (τ y)) ∨ y = (τ y) ∨ y = (σ y) := by grind
              clear b14e876737
              have b14e876755 : (M.op y y) = (τ y) ∨ y = (τ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b14e111 (τ y)
                   have i₂ := b14e876743
                   grind)
                | exact superpose b14e876743 b14e111
                | exact resolve b14e111 b14e876743
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e111 b14e876743
              have b14e876797 : (M.op x y) = (τ y) ∨ y = (τ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b14e876755
                   have i₂ := b14e106
                   grind)
                | exact superpose b14e106 b14e876755
                | exact resolve b14e876755 b14e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e876755
              have b14e879313 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (τ y)) ∨ y = (τ y) ∨ y = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e3049 x X0
                   have i₂ := b14e876797
                   grind)
                | exact superpose b14e876797 b14e3049
                | exact resolve b14e3049 b14e876797
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e876797
              have b14e879380 : ∀ X0 : G, y ≠ (M.op X0 (σ y)) ∨ y = (τ y) ∨ y = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e879313 X0
                   have i₂ := b14e17 y
                   grind)
                | exact superpose b14e17 b14e879313
                | exact resolve b14e879313 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879313
              have b14e879392 : y = (τ y) ∨ y = (σ y) := by
                first
                | (have r₁ := b14e879380 x
                   have r₂ := b14e875159 x
                   grind)
                | exact resolve b14e879380 b14e875159
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e875159 b14e879380
              have b14e879399 : y = (σ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b14e17 y
                   have i₂ := b14e879392
                   grind)
                | exact superpose b14e879392 b14e17
                | exact resolve b14e17 b14e879392
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879392
              have b14e879440 : y = (σ y) := by grind
              clear b14e879399
              have b14e879500 : ∀ X0 X1 : G, (M.op X0 y) ≠ (σ (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e3049 X1 X0
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e3049
                | exact resolve b14e3049 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e3049
              have b14e879519 : ∀ X0 : G, y = (k y (τ (M.op X0 y))) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e29842 X0
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e29842
                | exact resolve b14e29842 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29842
              have b14e879567 : y = (τ y) := by
                first
                | (have i₁ := b14e16 y
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e16
                | exact resolve b14e16 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e879568 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 y X0
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e21
                | exact resolve b14e21 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e880213 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = y := by
                intro X0
                first
                | (have i₁ := b14e874304 (σ X0)
                   have i₂ := b14e879568 X0
                   grind)
                | exact superpose b14e879568 b14e874304
                | (have j0 := b14e874304 (σ X0)
                   grind)
                | exact resolve b14e874304 b14e879568
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e874304 b14e879568
              have b14e887573 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op X1 y) ∨ (M.op y X0) = (k (M.op X1 y) X0) ∨ (M.op X1 y) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e874292 (M.op X0 y) X1
                   have i₂ := b14e222 X0 X1
                   grind)
                | exact superpose b14e222 b14e874292
                | (have j0 := b14e874292 (M.op y X0) (k (M.op X1 y) X0)
                   grind)
                | (have r₁ := b14e874292 (M.op y y) y
                   have r₂ := b14e222 y y
                   grind)
                | exact resolve b14e874292 b14e222
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e222 b14e874292
              have b14e887621 : ∀ X0 X1 : G, (M.op y X0) = (k (M.op X1 y) X0) ∨ (M.op X1 y) = X0 := by
                intro X0 X1
                first
                | (have j0 := b14e887573 X0 X1
                   have j1 := b14e5343 X1 X0
                   grind)
                | (have r₁ := b14e887573 y y
                   have r₂ := b14e5343 y y
                   grind)
                | (have r₁ := b14e887573 X1 X0
                   have r₂ := b14e5343 X0 X1
                   grind)
                | (have r₁ := b14e887573 y X1
                   have r₂ := b14e5343 y (M.op X1 y)
                   grind)
                | exact resolve b14e887573 b14e5343
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e5343 b14e887573
              have b14e887822 : ∀ X0 : G, (τ (M.op X0 y)) = (τ (M.op y y)) ∨ y = (M.op X0 y) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e34066 X0
                   have i₂ := b14e887621 y X0
                   grind)
                | exact superpose b14e887621 b14e34066
                | (have j0 := b14e34066 X0
                   have j1 := b14e887621 y X0
                   grind)
                | exact resolve b14e34066 b14e887621
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e34066 b14e887621
              have b14e887837 : ∀ X0 : G, (τ (M.op X0 y)) = (τ (M.op y y)) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have j0 := b14e887822 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e887822
              have b14e887848 : ∀ X0 : G, (τ (M.op x y)) = (τ (M.op X0 y)) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e887837 X0
                   have i₂ := b14e106
                   grind)
                | exact superpose b14e106 b14e887837
                | (have j0 := b14e887837 X0
                   grind)
                | exact resolve b14e887837 b14e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e106 b14e887837
              have b14e888110 : ∀ X0 : G, y = (k y (τ (M.op x y))) ∨ y = (M.op X0 y) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e879519 X0
                   have i₂ := b14e887848 X0
                   grind)
                | (have i₁ := b14e879519 x
                   have i₂ := b14e887848 X0
                   grind)
                | exact superpose b14e887848 b14e879519
                | (have j0 := b14e879519 x
                   have j1 := b14e887848 X0
                   grind)
                | exact resolve b14e879519 b14e887848
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879519 b14e887848
              have b14e888121 : ∀ X0 : G, y = (k y (τ (M.op x y))) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have j0 := b14e888110 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e888110
              have b14e888137 : ∀ X0 X1 : G, y = (k y (τ (M.op X0 y))) ∨ y = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e888121 X1
                   have i₂ := b14e136 x X0
                   grind)
                | (have i₁ := b14e888121 X1
                   have i₂ := b14e136 X0 x
                   grind)
                | exact superpose b14e136 b14e888121
                | (have j0 := b14e888121 X1
                   grind)
                | exact resolve b14e888121 b14e136
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e136
              have b14e888214 : ∀ X0 : G, (σ y) ≠ (M.op X0 y) ∨ y = (k y (τ (M.op x y))) := by
                intro X0
                first
                | (have i₁ := b14e879500 X0 x
                   have i₂ := b14e888121 x
                   grind)
                | exact superpose b14e888121 b14e879500
                | exact resolve b14e879500 b14e888121
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e888121
              have b14e888270 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y (τ (M.op x y))) := by
                intro X0
                first
                | (have i₁ := b14e888214 X0
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e888214
                | exact resolve b14e888214 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e888214
              have b14e888279 : y = (k y (τ (M.op x y))) := by
                first
                | (have j1 := b14e888137 x x
                   grind)
                | (have r₁ := b14e888270 x
                   have r₂ := b14e888137 x x
                   grind)
                | exact resolve b14e888270 b14e888137
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e888137 b14e888270
              have b14e888320 : (σ y) = (k (σ y) (M.op x y)) := by
                first
                | (have i₁ := b14e32 (M.op x y) y
                   have i₂ := b14e888279
                   grind)
                | exact superpose b14e888279 b14e32
                | exact resolve b14e32 b14e888279
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32 b14e888279
              have b14e888344 : y = (k y (M.op x y)) := by
                first
                | (have i₁ := b14e888320
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e888320
                | exact resolve b14e888320 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e888320
              have b14e888413 : (σ y) = (M.op y (σ (M.op x y))) ∨ y = (σ (M.op x y)) := by
                first
                | (have i₁ := b14e880213 (M.op x y)
                   have i₂ := b14e888344
                   grind)
                | exact superpose b14e888344 b14e880213
                | (have j0 := b14e880213 (M.op x y)
                   grind)
                | exact resolve b14e880213 b14e888344
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e880213 b14e888344
              have b14e888431 : y = (M.op y (σ (M.op x y))) ∨ y = (σ (M.op x y)) := by
                first
                | (have i₁ := b14e888413
                   have i₂ := b14e879440
                   grind)
                | exact superpose b14e879440 b14e888413
                | exact resolve b14e888413 b14e879440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879440 b14e888413
              have b14e905249 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X1 X1)) y) ∨ y = (σ (M.op x y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e8613 X0 X1 (σ (M.op x y))
                   have i₂ := b14e888431
                   grind)
                | exact superpose b14e888431 b14e8613
                | exact resolve b14e8613 b14e888431
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e8613 b14e888431
              have b14e905269 : y = (σ (M.op x y)) := by
                first
                | (have r₁ := b14e905249 x x
                   have r₂ := b14e879500 (M.op x (M.op x x)) x
                   grind)
                | exact resolve b14e905249 b14e879500
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e905249
              have b14e905334 : ∀ X0 : G, y ≠ (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e879500 X0 x
                   have i₂ := b14e905269
                   grind)
                | exact superpose b14e905269 b14e879500
                | exact resolve b14e879500 b14e905269
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879500
              have b14e905348 : (M.op x y) = (τ y) := by
                first
                | (have i₁ := b14e16 (M.op x y)
                   have i₂ := b14e905269
                   grind)
                | exact superpose b14e905269 b14e16
                | exact resolve b14e16 b14e905269
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e905269
              have b14e905439 : y = (M.op x y) := by
                first
                | (have i₁ := b14e905348
                   have i₂ := b14e879567
                   grind)
                | exact superpose b14e879567 b14e905348
                | exact resolve b14e905348 b14e879567
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e879567 b14e905348
              have b14e905463 : False := by grind
              exact b14e905463
        · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
          · have b15e18 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e22 : x ≠ y := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e24 : (σ x) ≠ (σ y) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e29 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e21
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e21
              | exact resolve b15e21 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e49 : x = (k x y) ∨ x = y := by grind
            have b15e52 : x = (k x y) := by
              first
              | (have r₁ := b15e49
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e49 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e49
            have b15e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | (have i₁ := b15e25
                 have i₂ := b15e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 (σ x) X0
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ y) (M.op (σ x) (σ x))
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (M.op (σ x) (σ x)) (σ y)
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e291 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have j0 := b15e63 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e63
            have b15e292 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e291
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e291 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e291
            have b15e293 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e292
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e292
              | exact resolve b15e292 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e292
            have b15e294 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e293
                 have i₂ := b15e52
                 grind)
              | exact superpose b15e52 b15e293
              | exact resolve b15e293 b15e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e52 b15e293
            have b15e295 : False := by grind
            exact b15e295
          · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e27 : x ≠ (M.op x y) := by grind
              have b16e28 : x = (M.op (M.op x y) (M.op x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e36 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 (M.op x y) X1
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e37 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b16e15 x X0 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e72 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
                intro X0
                first
                | (have i₁ := b16e36 x (M.op (M.op X0 x) X0)
                   have i₂ := b16e36 X0 x
                   grind)
                | exact superpose b16e36 b16e36
                | exact resolve b16e36 b16e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e84 : (M.op x x) = (M.op y x) := by
                first
                | (have i₁ := b16e36 (M.op y x) (M.op y x)
                   have i₂ := b16e37 (M.op y x)
                   grind)
                | exact superpose b16e37 b16e36
                | exact resolve b16e36 b16e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36 b16e37
              have b16e89 : y = (M.op y x) := by
                first
                | (have i₁ := b16e84
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e84
                | exact resolve b16e84 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e84
              have b16e126 : x = (M.op x y) := by
                first
                | (have i₁ := b16e72 y
                   have i₂ := b16e89
                   grind)
                | exact superpose b16e89 b16e72
                | exact resolve b16e72 b16e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e72 b16e89
              have b16e130 : False := by grind
              exact b16e130
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
                intro X0 X1 X2
                grind
              have b17e19 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : x ≠ y := by grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e25 : (σ x) ≠ (σ y) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e35 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 x X1
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
                   have i₂ := b17e15 X0 (M.op (M.op X0 X2) X0) X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e42 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e35 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
                   have i₂ := b17e15 X0 (M.op (M.op X0 X1) X0) X1
                   grind)
                | exact superpose b17e15 b17e35
                | exact resolve b17e35 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e44 : x = (k x y) ∨ x = y := by grind
              have b17e45 : x = (k x y) := by
                first
                | (have r₁ := b17e44
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e44 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e44
              have b17e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
                intro X0
                first
                | (have i₁ := b17e26
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e26
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e26
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (σ y) (M.op (σ x) (σ x))
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (M.op (σ x) (σ x)) (σ y)
                   grind)
                | exact resolve b17e26 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e88 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
                intro X0
                first
                | (have i₁ := b17e35 X0 x
                   have i₂ := b17e42 X0 x
                   grind)
                | exact superpose b17e42 b17e35
                | exact resolve b17e35 b17e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e152 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X0) X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e42 X1 x
                   have i₂ := b17e38 X1 X0 x
                   grind)
                | (have i₁ := b17e42 X0 X0
                   have i₂ := b17e38 X0 X0 x
                   grind)
                | exact superpose b17e38 b17e42
                | exact resolve b17e42 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e153 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X0) X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e35 X1 x
                   have i₂ := b17e38 X1 X0 x
                   grind)
                | (have i₁ := b17e35 X0 X0
                   have i₂ := b17e38 X0 X0 x
                   grind)
                | exact superpose b17e38 b17e35
                | exact resolve b17e35 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35 b17e38
              have b17e379 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have j0 := b17e56 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56
              have b17e380 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e379
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e379 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e379
              have b17e381 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e380
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e380
                | exact resolve b17e380 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e380
              have b17e382 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e381
                   have i₂ := b17e45
                   grind)
                | exact superpose b17e45 b17e381
                | exact resolve b17e381 b17e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e45 b17e381
              have b17e385 : (M.op (σ x) (σ x)) = (M.op y (σ x)) := by
                first
                | (have i₁ := b17e42 (σ x) (σ y)
                   have i₂ := b17e382
                   grind)
                | exact superpose b17e382 b17e42
                | exact resolve b17e42 b17e382
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e42
              have b17e2283 : (σ y) ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e385
                   grind)
                | exact superpose b17e385 b17e26
                | exact resolve b17e26 b17e385
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e2298 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (σ x)) X0) := by
                intro X0
                first
                | (have i₁ := b17e152 (σ x) X0
                   have i₂ := b17e385
                   grind)
                | exact superpose b17e385 b17e152
                | exact resolve b17e152 b17e385
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e152 b17e385
              have b17e2924 : ∀ X0 : G, (M.op y (M.op (M.op y (M.op y (σ x))) X0)) = X0 := by
                intro X0
                first
                | (have i₁ := b17e153 (M.op y (σ x)) X0
                   have i₂ := b17e2298 (M.op y (σ x))
                   grind)
                | exact superpose b17e2298 b17e153
                | exact resolve b17e153 b17e2298
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e153 b17e2298
              have b17e2968 : ∀ X0 : G, (M.op y (M.op (σ x) X0)) = X0 := by
                intro X0
                first
                | (have i₁ := b17e2924 X0
                   have i₂ := b17e88 (σ x)
                   grind)
                | exact superpose b17e88 b17e2924
                | exact resolve b17e2924 b17e88
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e88 b17e2924
              have b17e3048 : (σ y) = (M.op y (σ x)) := by
                first
                | (have i₁ := b17e2968 (σ y)
                   have i₂ := b17e382
                   grind)
                | exact superpose b17e382 b17e2968
                | exact resolve b17e2968 b17e382
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e382 b17e2968
              have b17e3090 : False := by grind
              exact b17e3090
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e21 : x ≠ y := by grind
          have b18e23 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e29 : y = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 y
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e14
            | exact resolve b18e14 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e30 : x = y := by
            first
            | (have i₁ := b18e29
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e29
            | exact resolve b18e29 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e31 : False := by grind
          exact b18e31
        · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e22 : x ≠ y := by grind
            have b19e24 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 y
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e15
              | exact resolve b19e15 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e31 : x = y := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e30
              | exact resolve b19e30 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : False := by grind
            exact b19e32
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e22 : x ≠ y := by grind
            have b20e24 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e15
              | exact resolve b20e15 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e31 : x = y := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e32 : False := by grind
            exact b20e32
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
              intro X0 X1 X2
              grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e41 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b21e14 x X0 y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e44 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
                 have i₂ := b21e14 X0 (M.op (M.op X0 X2) X0) X2
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e48 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 (M.op x x) X1
                 have i₂ := b21e41 x
                 grind)
              | exact superpose b21e41 b21e14
              | exact resolve b21e14 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e120 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b21e44 X0 (M.op x x) X1
                 have i₂ := b21e41 x
                 grind)
              | exact superpose b21e41 b21e44
              | exact resolve b21e44 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e41 b21e44
            have b21e297 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
              intro X0
              first
              | (have i₁ := b21e48 X0 x
                 have i₂ := b21e120 X0 x
                 grind)
              | exact superpose b21e120 b21e48
              | exact resolve b21e48 b21e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e48 b21e120
            have b21e657 : y = (M.op x x) := by
              first
              | (have i₁ := b21e297 y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e297
              | exact resolve b21e297 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e297
            have b21e670 : False := by grind
            exact b21e670
          · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : x ≠ y := by grind
              have b22e24 : y ≠ (M.op x x) := by grind
              have b22e25 : (σ x) ≠ (σ y) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b22e27 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e47 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
              have b22e50 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e47
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e47 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e47
              have b22e51 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e50
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e50
                | exact resolve b22e50 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e50
              have b22e54 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e51
                   grind)
                | exact superpose b22e51 b22e16
                | exact resolve b22e16 b22e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e51
              have b22e55 : x = (k x y) := by
                first
                | (have i₁ := b22e54
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e54
                | exact resolve b22e54 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e54
              have b22e76 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e55
                   grind)
                | exact superpose b22e55 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e55
              have b22e77 : y = (M.op x x) ∨ x = y := by
                first
                | (have r₁ := b22e76
                   have r₂ := b22e27
                   grind)
                | exact resolve b22e76 b22e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e76
              have b22e79 : x = y := by
                first
                | (have r₁ := b22e77
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e77 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e77
              have b22e81 : False := by grind
              exact b22e81
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : x ≠ y := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ x) ≠ (σ y) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b23e27 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e45 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
              have b23e48 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e45
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e45 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e45
              have b23e49 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e48
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e48
                | exact resolve b23e48 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e48
              have b23e52 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e49
                   grind)
                | exact superpose b23e49 b23e16
                | exact resolve b23e16 b23e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e49
              have b23e53 : x = (k x y) := by
                first
                | (have i₁ := b23e52
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e52
                | exact resolve b23e52 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e52
              have b23e72 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e53
                   grind)
                | exact superpose b23e53 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e53
              have b23e73 : y = (M.op x x) ∨ x = y := by
                first
                | (have r₁ := b23e72
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e72 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e72
              have b23e75 : x = y := by
                first
                | (have r₁ := b23e73
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e73 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e73
              have b23e77 : False := by grind
              exact b23e77
        · rcases eq_or_ne ((M.op x y)) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
              intro X0 X1 X2
              grind
            have b24e23 : y ≠ (M.op x x) := by grind
            have b24e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e40 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b24e14 x X0 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e45 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 (M.op x x) X1
                 have i₂ := b24e40 x
                 grind)
              | exact superpose b24e40 b24e14
              | exact resolve b24e14 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e40
            have b24e85 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e45 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
                 have i₂ := b24e14 X0 (M.op (M.op X0 X1) X0) X1
                 grind)
              | exact superpose b24e14 b24e45
              | exact resolve b24e45 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e187 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e45 X0 x
                 have i₂ := b24e85 X0 x
                 grind)
              | exact superpose b24e85 b24e45
              | exact resolve b24e45 b24e85
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e45 b24e85
            have b24e259 : y = (M.op x x) := by
              first
              | (have i₁ := b24e187 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e187
              | exact resolve b24e187 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e187
            have b24e268 : False := by grind
            exact b24e268
          · rcases eq_or_ne (M.op (M.op x y) (M.op x y)) (x) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : x ≠ y := by grind
              have b25e24 : y ≠ (M.op x x) := by grind
              have b25e25 : (σ x) ≠ (σ y) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X0 X1
                   have i₂ := b25e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e827 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e51 x y
                   grind)
                | exact superpose b25e51 b25e22
                | (have j1 := b25e51 x y
                   grind)
                | exact resolve b25e22 b25e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e51
              have b25e873 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
                first
                | (have r₁ := b25e827
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e827 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e827
              have b25e886 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b25e873
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e873 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e873
              have b25e941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b25e886
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e886
                | (have j1 := b25e20 x y
                   grind)
                | (have r₁ := b25e886
                   have r₂ := b25e20 (σ (M.op x y)) (σ (k x y))
                   grind)
                | (have r₁ := b25e886
                   have r₂ := b25e20 (σ (k x y)) (σ (M.op x y))
                   grind)
                | exact resolve b25e886 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e886
              have b25e942 : y = (M.op x x) ∨ x = y := by grind
              clear b25e941
              have b25e946 : x = y := by
                first
                | (have r₁ := b25e942
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e942 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e942
              have b25e950 : False := by grind
              exact b25e950
            · have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : x ≠ y := by grind
              have b26e24 : y ≠ (M.op x x) := by grind
              have b26e25 : (σ x) ≠ (σ y) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | (have i₁ := b26e26
                   have i₂ := b26e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ y) (M.op (σ x) (σ x))
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (M.op (σ x) (σ x)) (σ y)
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e268 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have j0 := b26e64 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64
              have b26e269 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e268
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e268 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e268
              have b26e270 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e269
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e269
                | exact resolve b26e269 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e269
              have b26e271 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e270
                   grind)
                | exact superpose b26e270 b26e22
                | exact resolve b26e22 b26e270
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e270
              have b26e336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b26e271
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e271
                | (have j1 := b26e20 x y
                   grind)
                | (have r₁ := b26e271
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k x y))
                   grind)
                | (have r₁ := b26e271
                   have r₂ := b26e20 (σ (k x y)) (σ (M.op x y))
                   grind)
                | exact resolve b26e271 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e271
              have b26e337 : y = (M.op x x) ∨ x = y := by grind
              clear b26e336
              have b26e339 : x = y := by
                first
                | (have r₁ := b26e337
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e337 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e337
              have b26e341 : False := by grind
              exact b26e341

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e27
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : x = y := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e25
          | exact resolve b3e25 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
               have i₂ := b4e13 X0 (M.op (M.op X0 X2) X0) X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e33
            | exact resolve b4e33 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e39 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op y y) X1
               have i₂ := b4e32 y
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e87 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
               have i₂ := b4e13 X0 (M.op (M.op X0 X1) X0) X1
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e97 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X2) X1)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (σ X0) X2
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op y X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e97 X0 X1 x
               have i₂ := b4e87 X1 x
               grind)
            | exact superpose b4e87 b4e97
            | exact resolve b4e97 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97
          have b4e110 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e35 (σ y) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X3 X3) (M.op X1 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e35 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e155 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e110 X0
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e110
            | exact resolve b4e110 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e110
          have b4e156 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e87 y (M.op (M.op X0 x) X0)
               have i₂ := b4e39 X0 x
               grind)
            | exact superpose b4e39 b4e87
            | exact resolve b4e87 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e168 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X2 X2) X0) := by
            intro X0 X2
            first
            | (have i₁ := b4e35 X0 X2 x
               have i₂ := b4e87 X0 x
               grind)
            | exact superpose b4e87 b4e35
            | exact resolve b4e35 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e169 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e39 X0 x
               have i₂ := b4e87 X0 x
               grind)
            | exact superpose b4e87 b4e39
            | exact resolve b4e39 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e270 : x = (M.op y y) := by
            first
            | (have i₁ := b4e169 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e169
            | exact resolve b4e169 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e333 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e270
               grind)
            | exact superpose b4e270 b4e36
            | exact resolve b4e36 b4e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e355 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e333 x
               have i₂ := b4e168 (σ x) x
               grind)
            | exact superpose b4e168 b4e333
            | exact resolve b4e333 b4e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168 b4e333
          have b4e665 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e100 y X0
               have i₂ := b4e270
               grind)
            | exact superpose b4e270 b4e100
            | exact resolve b4e100 b4e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100
          have b4e1620 : ∀ X0 : G, (M.op y (σ x)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e87 (σ x) (M.op y X0)
               have i₂ := b4e665 X0
               grind)
            | exact superpose b4e665 b4e87
            | exact resolve b4e87 b4e665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87 b4e665
          have b4e1627 : ∀ X0 : G, (σ y) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e1620 X0
               have i₂ := b4e355
               grind)
            | exact superpose b4e355 b4e1620
            | exact resolve b4e1620 b4e355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e355 b4e1620
          have b4e1773 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ y)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e112 X0 (σ x) x
               have i₂ := b4e1627 (σ x)
               grind)
            | exact superpose b4e1627 b4e112
            | exact resolve b4e112 b4e1627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112 b4e1627
          have b4e1821 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1773 X0 x
               have i₂ := b4e155 x
               grind)
            | exact superpose b4e155 b4e1773
            | exact resolve b4e1773 b4e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155 b4e1773
          have b4e1835 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1821 X0
               have i₂ := b4e270
               grind)
            | exact superpose b4e270 b4e1821
            | exact resolve b4e1821 b4e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1821
          have b4e2024 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1835 (σ x)
               grind)
            | exact superpose b4e1835 b4e20
            | exact resolve b4e20 b4e1835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1835
          have b4e2031 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e2024
               have i₂ := b4e156 x
               grind)
            | exact superpose b4e156 b4e2024
            | exact resolve b4e2024 b4e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156 b4e2024
          have b4e2056 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e2031
               have i₂ := b4e270
               grind)
            | exact superpose b4e270 b4e2031
            | exact resolve b4e2031 b4e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270 b4e2031
          have b4e2057 : False := by grind
          exact b4e2057
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op y y) X1
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e39 : y ≠ y ∨ x = y ∨ x = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : x = y ∨ x = (k x y) := by grind
          clear b5e39
          have b5e43 : x = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e21
               grind)
            | exact resolve b5e42 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e80 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
               have i₂ := b5e13 X0 (M.op (M.op X0 X1) X0) X1
               grind)
            | exact superpose b5e13 b5e37
            | exact resolve b5e37 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e146 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e80 y (M.op (M.op X0 x) X0)
               have i₂ := b5e37 X0 x
               grind)
            | exact superpose b5e37 b5e80
            | exact resolve b5e80 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e158 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e37 X0 x
               have i₂ := b5e80 X0 x
               grind)
            | exact superpose b5e80 b5e37
            | exact resolve b5e37 b5e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e80
          have b5e249 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e46 x y
               grind)
            | exact superpose b5e46 b5e20
            | (have j1 := b5e46 x y
               grind)
            | exact resolve b5e20 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e276 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e249
               have r₂ := b5e24
               grind)
            | exact resolve b5e249 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249
          have b5e284 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b5e276
               have r₂ := b5e23
               grind)
            | exact resolve b5e276 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e276
          have b5e285 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e284
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e284
            | exact resolve b5e284 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e284
          have b5e286 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e285
               have i₂ := b5e146 x
               grind)
            | exact superpose b5e146 b5e285
            | exact resolve b5e285 b5e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146 b5e285
          have b5e299 : x = (M.op y y) := by
            first
            | (have i₁ := b5e158 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e158
            | exact resolve b5e158 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e158
          have b5e323 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e286
               have i₂ := b5e299
               grind)
            | exact superpose b5e299 b5e286
            | exact resolve b5e286 b5e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e286 b5e299
          have b5e340 : False := by grind
          exact b5e340
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : x = y := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e34 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
               have i₂ := b7e13 X0 (M.op (M.op X0 X2) X0) X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e51 : x = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e64 : x = (M.op x y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e79 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 y
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e13
            | exact resolve b7e13 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e138 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 (M.op x x) X1
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e34
            | exact resolve b7e34 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e139 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op x x) X1
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e13
            | exact resolve b7e13 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e358 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e139 X0 x
               have i₂ := b7e138 X0 x
               grind)
            | exact superpose b7e138 b7e139
            | exact resolve b7e139 b7e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e686 : y = (M.op x x) := by
            first
            | (have i₁ := b7e358 y
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e358
            | exact resolve b7e358 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e358
          have b7e815 : y = (M.op y x) := by
            first
            | (have i₁ := b7e138 x x
               have i₂ := b7e686
               grind)
            | exact superpose b7e686 b7e138
            | exact resolve b7e138 b7e686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138 b7e686
          have b7e817 : False := by grind
          exact b7e817
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e140 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e55 x y
               grind)
            | exact superpose b8e55 b8e20
            | (have j1 := b8e55 x y
               grind)
            | exact resolve b8e20 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e140
               have r₂ := b8e24
               grind)
            | exact resolve b8e140 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e168 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e159
               have r₂ := b8e23
               grind)
            | exact resolve b8e159 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159
          have b8e173 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e168
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e168
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e168
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e168
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e168 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168
          have b8e174 : y = (M.op y x) ∨ x = y := by grind
          clear b8e173
          have b8e175 : x = y := by
            first
            | (have r₁ := b8e174
               have r₂ := b8e22
               grind)
            | exact resolve b8e174 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e176 : False := by grind
          exact b8e176

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_x_x_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e18
        | exact resolve b0e18 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e63 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e62
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e62
        | exact resolve b0e62 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e66 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e63
           have i₂ := b0e26 x
           grind)
        | exact superpose b0e26 b0e63
        | exact resolve b0e63 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e63
      have b0e67 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e66
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e66
        | exact resolve b0e66 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e68 : False := by grind
      exact b0e68
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e83 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e85 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e83 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83
        have b1e146 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e36 X1 X0
             grind)
          | exact superpose b1e36 b1e13
          | exact resolve b1e13 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e205 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e85 X0
             have i₂ := b1e53 X0 X1
             grind)
          | (have i₁ := b1e85 X0
             have i₂ := b1e53 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e53 b1e85
          | (have j1 := b1e53 X1 X0
             grind)
          | exact resolve b1e85 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e85
        have b1e220 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e205 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e205
        have b1e231 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e146
        have b1e245 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e231 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e231
          | exact resolve b1e231 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e231
        have b1e504 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e220 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e220
        have b1e686 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b1e504 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e504
          | (have j0 := b1e504 x x
             grind)
          | exact resolve b1e504 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e504
        have b1e1737 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e63 x x
             grind)
          | exact superpose b1e63 b1e21
          | (have j1 := b1e63 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e63 x y
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e63 y x
             grind)
          | exact resolve b1e21 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1860 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e63 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e1861 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e1860 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1860
        have b1e1882 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e1737
        have b1e4037 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1882
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e1882
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e1882 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1882
        have b1e4050 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e4037
        have b1e4071 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e4050
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e4050
          | exact resolve b1e4050 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4050
        have b1e4072 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e4071
        have b1e4087 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e4072
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e4072
          | exact resolve b1e4072 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4072
        have b1e4118 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e245 x
             have i₂ := b1e4087
             grind)
          | exact superpose b1e4087 b1e245
          | exact resolve b1e245 b1e4087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e245 b1e4087
        have b1e4164 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e4118
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e4118
          | exact resolve b1e4118 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4118
        have b1e4165 : x = (k x x) := by
          first
          | (have r₁ := b1e4164
             have r₂ := b1e686
             grind)
          | exact resolve b1e4164 b1e686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e686 b1e4164
        have b1e4203 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e1861 x
             have i₂ := b1e4165
             grind)
          | exact superpose b1e4165 b1e1861
          | (have j0 := b1e1861 x
             grind)
          | exact resolve b1e1861 b1e4165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1861
        have b1e4204 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e4165
             grind)
          | exact superpose b1e4165 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e4165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4165
        have b1e4217 : x = (M.op x x) := by grind
        clear b1e4204
        have b1e4218 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e4203
        have b1e4347 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e4217
             grind)
          | exact superpose b1e4217 b1e20
          | exact resolve b1e20 b1e4217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4217
        have b1e5518 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e4218
             grind)
          | exact superpose b1e4218 b1e21
          | exact resolve b1e21 b1e4218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4218
        have b1e5573 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e5518
             have i₂ := b1e4347
             grind)
          | exact superpose b1e4347 b1e5518
          | exact resolve b1e5518 b1e4347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4347 b1e5518
        have b1e5574 : False := by grind
        exact b1e5574
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x = (k x y) := by grind
        have b2e26 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e50 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e32 X1 X0
             grind)
          | exact superpose b2e32 b2e13
          | exact resolve b2e13 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e82 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e84 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e82 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e124 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e84 X0
             have i₂ := b2e47 X0 X1
             grind)
          | (have i₁ := b2e84 X0
             have i₂ := b2e47 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e47 b2e84
          | (have j1 := b2e47 X1 X0
             grind)
          | exact resolve b2e84 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e84
        have b2e137 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e124 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124
        have b2e281 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e68
        have b2e301 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e281 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e281
          | exact resolve b2e281 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e281
        have b2e538 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e50 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e539 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e538
             have r₂ := b2e22
             grind)
          | exact resolve b2e538 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e538
        have b2e540 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e539
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e539
          | exact resolve b2e539 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e539
        have b2e541 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e540
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e540
          | exact resolve b2e540 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e540
        have b2e544 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e541
             grind)
          | exact superpose b2e541 b2e19
          | exact resolve b2e19 b2e541
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e541
        have b2e548 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e544
             have i₂ := b2e26 x
             grind)
          | exact superpose b2e26 b2e544
          | exact resolve b2e544 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e544
        have b2e549 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e548
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e548
          | exact resolve b2e548 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e548
        have b2e744 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e137 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137
        have b2e770 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e744 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e744
          | (have j0 := b2e744 x x
             grind)
          | exact resolve b2e744 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e744
        have b2e1306 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e57 x x
             grind)
          | exact superpose b2e57 b2e21
          | (have j1 := b2e57 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e57 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e57 y x
             grind)
          | exact resolve b2e21 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e1434 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1306
        have b2e3693 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1434
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e1434
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e1434 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1434
        have b2e3706 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e3693
        have b2e3727 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e3706
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3706
          | exact resolve b2e3706 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3706
        have b2e3728 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e3727
        have b2e3743 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e3728
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3728
          | exact resolve b2e3728 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3728
        have b2e3774 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e301 x
             have i₂ := b2e3743
             grind)
          | exact superpose b2e3743 b2e301
          | exact resolve b2e301 b2e3743
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e301 b2e3743
        have b2e3821 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e3774
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e3774
          | exact resolve b2e3774 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3774
        have b2e3822 : x = (k x x) := by
          first
          | (have r₁ := b2e3821
             have r₂ := b2e770
             grind)
          | exact resolve b2e3821 b2e770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e770 b2e3821
        have b2e3860 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e3822
             grind)
          | exact superpose b2e3822 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e3822
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3822
        have b2e3873 : x = (M.op x x) := by grind
        clear b2e3860
        have b2e4010 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e3873
             grind)
          | exact superpose b2e3873 b2e20
          | exact resolve b2e20 b2e3873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3873
        have b2e4096 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e549
             have i₂ := b2e4010
             grind)
          | exact superpose b2e4010 b2e549
          | exact resolve b2e549 b2e4010
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e549 b2e4010
        have b2e4113 : False := by grind
        exact b2e4113
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : x = (M.op y x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e28 y
             grind)
          | exact superpose b3e28 b3e21
          | exact resolve b3e21 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e60 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e17 (σ X0) (σ X1)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e83 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b3e85 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b3e83 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e237 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e85 X0
             have i₂ := b3e60 X0 X1
             grind)
          | (have i₁ := b3e85 X0
             have i₂ := b3e60 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e60 b3e85
          | (have j1 := b3e60 X1 X0
             grind)
          | exact resolve b3e85 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e85
        have b3e251 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e237 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e237
        have b3e1460 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e64 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e64
          | exact resolve b3e64 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e1702 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e1460
        have b3e1912 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e1702
             grind)
          | exact superpose b3e1702 b3e13
          | exact resolve b3e13 b3e1702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1702
        have b3e1932 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1912
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1912
          | exact resolve b3e1912 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1912
        have b3e2176 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e251 x x
             have i₂ := b3e1932
             grind)
          | exact superpose b3e1932 b3e251
          | exact resolve b3e251 b3e1932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e251 b3e1932
        have b3e2179 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b3e2176
             have r₂ := b3e20
             grind)
          | exact resolve b3e2176 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2176
        have b3e2437 : y = (τ (σ x)) ∨ x = y := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e2179
             grind)
          | exact superpose b3e2179 b3e13
          | exact resolve b3e13 b3e2179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2179
        have b3e2456 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e2437
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2437
          | exact resolve b3e2437 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2437
        have b3e2457 : x = y := by grind
        clear b3e2456
        have b3e2718 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e2457
             grind)
          | exact superpose b3e2457 b3e19
          | exact resolve b3e19 b3e2457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2723 : x = (M.op x x) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e2457
             grind)
          | exact superpose b3e2457 b3e43
          | exact resolve b3e43 b3e2457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e2728 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e2718
             have i₂ := b3e2723
             grind)
          | exact superpose b3e2723 b3e2718
          | exact resolve b3e2718 b3e2723
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2718 b3e2723
        have b3e2729 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e2728
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e2728
          | exact resolve b3e2728 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2728
        have b3e2730 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e2729
             have i₂ := b3e2457
             grind)
          | exact superpose b3e2457 b3e2729
          | exact resolve b3e2729 b3e2457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2457 b3e2729
        have b3e2731 : False := by grind
        exact b3e2731
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X0)) := by
            intro X0 X1
            grind
          have b4e35 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19
            | exact resolve b4e19 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e58 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 X2
               have i₂ := b4e18 X0 X2
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 (M.op X1 X2) X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X2
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e31 (σ x)
               grind)
            | exact superpose b4e31 b4e20
            | exact resolve b4e20 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e77 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e75
            | exact resolve b4e75 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e75
          have b4e99 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b4e101 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b4e99 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e149 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e35 X1 X0
               grind)
            | exact superpose b4e35 b4e14
            | exact resolve b4e14 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e241 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e101 X0
               have i₂ := b4e57 X0 X1
               grind)
            | (have i₁ := b4e101 X0
               have i₂ := b4e57 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e57 b4e101
            | (have j1 := b4e57 X1 X0
               grind)
            | exact resolve b4e101 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57 b4e101
          have b4e256 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e241 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e241
          have b4e797 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          clear b4e58
          have b4e1033 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e149 X0 X1
               have i₂ := b4e256 (σ X0) X1
               grind)
            | exact superpose b4e256 b4e149
            | (have j1 := b4e256 (σ X0) X1
               grind)
            | exact resolve b4e149 b4e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149 b4e256
          have b4e1054 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1033 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e1033
            | (have j0 := b4e1033 X0 X1
               grind)
            | exact resolve b4e1033 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1033
          have b4e1844 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e63 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e1845 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e1844 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1844
          have b4e6321 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e1054 X1 (σ X0)
               grind)
            | exact superpose b4e1054 b4e19
            | (have j1 := b4e1054 X1 (σ X0)
               grind)
            | exact resolve b4e19 b4e1054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1054
          have b4e6346 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e6321 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e6321
            | (have j0 := b4e6321 X0 X1
               grind)
            | exact resolve b4e6321 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6321
          have b4e9358 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 X1 X1
               have i₂ := b4e797 X0 X1
               grind)
            | (have i₁ := b4e33 X0 X1
               have i₂ := b4e797 (M.op X0 X1) X1
               grind)
            | exact superpose b4e797 b4e33
            | (have j1 := b4e797 X0 X1
               grind)
            | exact resolve b4e33 b4e797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e797
          have b4e9407 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e9358 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9358
          have b4e18502 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e6346 x x
               grind)
            | exact superpose b4e6346 b4e77
            | (have j1 := b4e6346 x x
               grind)
            | exact resolve b4e77 b4e6346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6346
          have b4e21660 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e18502
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e18502
            | (have j1 := b4e18 x x
               grind)
            | exact resolve b4e18502 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18502
          have b4e21699 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e21660
          have b4e21700 : x = (M.op x x) := by grind
          clear b4e21699
          have b4e21801 : x = (k x x) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e9407 x x
               have i₂ := b4e21700
               grind)
            | exact superpose b4e21700 b4e9407
            | exact resolve b4e9407 b4e21700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9407
          have b4e21802 : x = (k x x) := by grind
          clear b4e21801
          have b4e23367 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e1845 x
               have i₂ := b4e21802
               grind)
            | exact superpose b4e21802 b4e1845
            | (have j0 := b4e1845 x
               grind)
            | exact resolve b4e1845 b4e21802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1845 b4e21802
          have b4e23396 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e23367
          have b4e25622 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e23396
               grind)
            | exact superpose b4e23396 b4e77
            | exact resolve b4e77 b4e23396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77 b4e23396
          have b4e25728 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e25622
               have i₂ := b4e21700
               grind)
            | exact superpose b4e21700 b4e25622
            | exact resolve b4e25622 b4e21700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21700 b4e25622
          have b4e25729 : False := by grind
          exact b4e25729
        · have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : y = (k y x) := by grind
          have b5e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e51 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ y) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ y) X0
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
          have b5e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e81 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e79 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e32 X1 X0
               grind)
            | exact superpose b5e32 b5e14
            | exact resolve b5e14 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e144 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e81 X0
               have i₂ := b5e47 X0 X1
               grind)
            | (have i₁ := b5e81 X0
               have i₂ := b5e47 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e47 b5e81
            | (have j1 := b5e47 X1 X0
               grind)
            | exact resolve b5e81 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e81
          have b5e157 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e144 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144
          have b5e228 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e108
          have b5e245 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e228 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e228
            | exact resolve b5e228 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e228
          have b5e549 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e157 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157
          have b5e565 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e51 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e566 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e565
               have r₂ := b5e23
               grind)
            | exact resolve b5e565 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e565
          have b5e567 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e566
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e566
            | exact resolve b5e566 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e566
          have b5e568 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e567
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e567
            | exact resolve b5e567 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e567
          have b5e750 : x ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e549 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e549
            | (have j0 := b5e549 y y
               grind)
            | exact resolve b5e549 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e549
          have b5e1372 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e58 y y
               grind)
            | exact superpose b5e58 b5e24
            | (have j1 := b5e58 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e58 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e58 x y
               grind)
            | exact resolve b5e24 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e1498 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1372
          have b5e3539 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e1498
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e1498
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e1498 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1498
          have b5e3552 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e3539
          have b5e3573 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e3552
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3552
            | exact resolve b5e3552 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3552
          have b5e3574 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e3573
          have b5e3589 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e3574
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3574
            | exact resolve b5e3574 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3574
          have b5e3623 : y = (k y (τ (σ y))) ∨ x = y := by
            first
            | (have i₁ := b5e245 y
               have i₂ := b5e3589
               grind)
            | exact superpose b5e3589 b5e245
            | exact resolve b5e245 b5e3589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e245 b5e3589
          have b5e3668 : y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e3623
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e3623
            | exact resolve b5e3623 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3623
          have b5e3669 : y = (k y y) := by
            first
            | (have r₁ := b5e3668
               have r₂ := b5e750
               grind)
            | exact resolve b5e3668 b5e750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e750 b5e3668
          have b5e3700 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e3669
               grind)
            | exact superpose b5e3669 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e3669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3669
          have b5e3713 : y = (M.op y y) := by grind
          clear b5e3700
          have b5e3733 : x = y := by
            first
            | (have i₁ := b5e3713
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3713
            | exact resolve b5e3713 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3713
          have b5e3871 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3733
               grind)
            | exact superpose b5e3733 b5e24
            | exact resolve b5e24 b5e3733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3879 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e568
               have i₂ := b5e3733
               grind)
            | exact superpose b5e3733 b5e568
            | exact resolve b5e568 b5e3733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e568 b5e3733
          have b5e3897 : False := by grind
          exact b5e3897
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e26 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e25
          | exact resolve b6e25 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e26
             grind)
          | exact superpose b6e26 b6e13
          | exact resolve b6e13 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : x = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e29 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e29 (σ x)
             grind)
          | exact superpose b6e29 b6e19
          | exact resolve b6e19 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e41 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e40
          | exact resolve b6e40 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e59 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e64 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e28
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e28 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X0 X1
             have i₂ := b6e17 (σ X0) (σ X1)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e68 : x = (M.op x y) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e64
             have r₂ := b6e20
             grind)
          | exact resolve b6e64 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e75 : x = (M.op x y) := by
          first
          | (have r₁ := b6e68
             have r₂ := b6e21
             grind)
          | exact resolve b6e68 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e77 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e75
             grind)
          | exact superpose b6e75 b6e41
          | exact resolve b6e41 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e75
        have b6e89 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e91 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e89 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e240 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e91 X0
             have i₂ := b6e59 X0 X1
             grind)
          | (have i₁ := b6e91 X0
             have i₂ := b6e59 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e59 b6e91
          | (have j1 := b6e59 X1 X0
             grind)
          | exact resolve b6e91 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e91
        have b6e254 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e240 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e240
        have b6e1541 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e66 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e66
          | exact resolve b6e66 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e1789 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1541
        have b6e1850 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e1789
             have r₂ := b6e77
             grind)
          | exact resolve b6e1789 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1789
        have b6e1901 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1850
             grind)
          | exact superpose b6e1850 b6e13
          | exact resolve b6e13 b6e1850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1850
        have b6e1921 : y = (k x x) := by
          first
          | (have i₁ := b6e1901
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1901
          | exact resolve b6e1901 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1901
        have b6e2000 : y = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e254 x x
             have i₂ := b6e1921
             grind)
          | exact superpose b6e1921 b6e254
          | exact resolve b6e254 b6e1921
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e254 b6e1921
        have b6e2003 : x = y := by
          first
          | (have r₁ := b6e2000
             have r₂ := b6e20
             grind)
          | exact resolve b6e2000 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2000
        have b6e2264 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e2003
             grind)
          | exact superpose b6e2003 b6e77
          | exact resolve b6e77 b6e2003
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77 b6e2003
        have b6e2271 : False := by grind
        exact b6e2271
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e65 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          have b7e101 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e103 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e101 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e106 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e94
               have r₂ := b7e23
               grind)
            | exact resolve b7e94 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e109 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e106
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e106
            | exact resolve b7e106 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e119 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e109
               grind)
            | exact superpose b7e109 b7e14
            | exact resolve b7e14 b7e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e120 : x = (k x y) := by
            first
            | (have i₁ := b7e119
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e119
            | exact resolve b7e119 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119
          have b7e135 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e120
               grind)
            | exact superpose b7e120 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120
          have b7e136 : x = (M.op x y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e135
               have r₂ := b7e21
               grind)
            | exact resolve b7e135 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135
          have b7e138 : x = (M.op x y) := by
            first
            | (have r₁ := b7e136
               have r₂ := b7e22
               grind)
            | exact resolve b7e136 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e241 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e103 X0
               have i₂ := b7e65 X0 X1
               grind)
            | (have i₁ := b7e103 X0
               have i₂ := b7e65 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e65 b7e103
            | (have j1 := b7e65 X1 X0
               grind)
            | exact resolve b7e103 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e103
          have b7e255 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e241 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e241
          have b7e1675 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e73 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e73
            | exact resolve b7e73 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e1934 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1675
          have b7e2123 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1934
               grind)
            | exact superpose b7e1934 b7e14
            | exact resolve b7e14 b7e1934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1934
          have b7e2138 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2123
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2123
            | exact resolve b7e2123 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2123
          have b7e2387 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e255 y y
               have i₂ := b7e2138
               grind)
            | exact superpose b7e2138 b7e255
            | exact resolve b7e255 b7e2138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e255 b7e2138
          have b7e2390 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e2387
               have r₂ := b7e22
               grind)
            | exact resolve b7e2387 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2387
          have b7e2678 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e2390
               grind)
            | exact superpose b7e2390 b7e14
            | exact resolve b7e14 b7e2390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2390
          have b7e2692 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e2678
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2678
            | exact resolve b7e2678 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2678
          have b7e2693 : x = y := by grind
          clear b7e2692
          have b7e2966 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e2693
               grind)
            | exact superpose b7e2693 b7e22
            | exact resolve b7e22 b7e2693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2980 : x = (M.op x x) := by
            first
            | (have i₁ := b7e138
               have i₂ := b7e2693
               grind)
            | exact superpose b7e2693 b7e138
            | exact resolve b7e138 b7e2693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138 b7e2693
          have b7e2985 : False := by grind
          exact b7e2985
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e47 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e499 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e47 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47
          have b8e500 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e499
               have r₂ := b8e24
               grind)
            | exact resolve b8e499 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e499
          have b8e501 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e500
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e500
            | exact resolve b8e500 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e500
          have b8e504 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e501
               grind)
            | exact superpose b8e501 b8e20
            | exact resolve b8e20 b8e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e501
          have b8e512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e504
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e504
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e504 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e521 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e512
          have b8e523 : x = (M.op y y) := by
            first
            | (have r₁ := b8e521
               have r₂ := b8e21
               grind)
            | exact resolve b8e521 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e521
          have b8e524 : False := by grind
          exact b8e524

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
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
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op X1 x)
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 x X0
           have i₂ := b0e33 x X1
           grind)
        | exact superpose b0e33 b0e33
        | exact resolve b0e33 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (M.op X0 X0)) := by
        intro X0
        grind
      have b0e44 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X1 X1
           have i₂ := b0e33 X1 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e49 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e40 X0
           have i₂ := b0e44 X0 X0
           grind)
        | exact superpose b0e44 b0e40
        | exact resolve b0e40 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e44
      have b0e84 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e49 X1
           have i₂ := b0e39 y X0
           grind)
        | (have i₁ := b0e49 X1
           have i₂ := b0e39 X0 y
           grind)
        | exact superpose b0e39 b0e49
        | exact resolve b0e49 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e49
      have b0e87 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        grind
      clear b0e24
      have b0e92 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e87 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e87
        | exact resolve b0e87 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        grind
      clear b0e92
      have b0e94 : False := by grind
      exact b0e94
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : x = y := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e26
            | exact resolve b4e26 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e28 : False := by grind
          exact b4e28
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e41 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X1 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b5e41 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e41
            | exact resolve b5e41 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e53 : y = (M.op x x) := by
            first
            | (have i₁ := b5e47
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e47
            | exact resolve b5e47 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e70 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b5e44 x X0
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e44
            | exact resolve b5e44 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e53
          have b5e89 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b5e70 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e70
            | exact resolve b5e70 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e101 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 (M.op x x) x x
               have i₂ := b5e89 (M.op x x)
               grind)
            | exact superpose b5e89 b5e13
            | exact resolve b5e13 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e138 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e89 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e89
            | exact resolve b5e89 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e149 : y = (σ y) := by
            first
            | (have i₁ := b5e138 x
               have i₂ := b5e89 x
               grind)
            | exact superpose b5e89 b5e138
            | exact resolve b5e138 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e138
          have b5e183 : y ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e149
               grind)
            | exact superpose b5e149 b5e24
            | exact resolve b5e24 b5e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e189 : False := by grind
          exact b5e189
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : x = y := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e56
          have b7e61 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e23
               grind)
            | exact resolve b7e59 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e62 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e61
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e61
            | exact resolve b7e61 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e71 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e62
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e62 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e72 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e26
               grind)
            | exact resolve b7e71 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e71
          have b7e73 : x = y := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e22
               grind)
            | exact resolve b7e72 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e74 : False := by grind
          exact b7e74
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e910 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e76 x y
               grind)
            | exact superpose b8e76 b8e20
            | (have j1 := b8e76 x y
               grind)
            | exact resolve b8e20 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e923 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e910
               have r₂ := b8e24
               grind)
            | exact resolve b8e910 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e910
          have b8e927 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e923
               have r₂ := b8e23
               grind)
            | exact resolve b8e923 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e923
          have b8e928 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e927
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e927
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e927
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e927
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e927 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e927
          have b8e929 : y = (M.op x y) ∨ x = y := by grind
          clear b8e928
          have b8e930 : x = y := by
            first
            | (have r₁ := b8e929
               have r₂ := b8e22
               grind)
            | exact resolve b8e929 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e929
          have b8e931 : False := by grind
          exact b8e931
