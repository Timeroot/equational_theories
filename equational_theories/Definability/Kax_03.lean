import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation314`: `x ◇ x = y ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation314 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law314 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law314.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e11
        | exact resolve b0e11 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e38 X0 x
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e38
        | exact resolve b0e38 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e55 : y = (σ y) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e39 (σ x)
           grind)
        | exact superpose b0e39 b0e20
        | exact resolve b0e20 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e86 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e18
        | exact resolve b0e18 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e91 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e86
           have i₂ := b0e27 (σ x)
           grind)
        | exact superpose b0e27 b0e86
        | exact resolve b0e86 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86
      have b0e92 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e91
           have i₂ := b0e27 x
           grind)
        | exact superpose b0e27 b0e91
        | exact resolve b0e91 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e91
      have b0e93 : False := by grind
      exact b0e93
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : x = (k x y) := by grind
        have b1e28 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e28 x
             grind)
          | exact superpose b1e28 b1e24
          | exact resolve b1e24 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e28
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e52 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e51
          | exact resolve b1e51 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e51
        have b1e53 : False := by grind
        exact b1e53
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 y
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b2e35 X0 x
             have i₂ := b2e27 x
             grind)
          | exact superpose b2e27 b2e35
          | exact resolve b2e35 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e35
        have b2e37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e42 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          grind
        have b2e45 : y ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e36 (σ x)
             grind)
          | exact superpose b2e36 b2e21
          | exact resolve b2e21 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e194 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e37 X0 y
             have i₂ := b2e42 (τ X0)
             grind)
          | exact superpose b2e42 b2e37
          | exact resolve b2e37 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e42
        have b2e198 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e194 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e194
          | exact resolve b2e194 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e194
        have b2e216 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e17 X0 (σ y)
             have i₂ := b2e198 X0
             grind)
          | exact superpose b2e198 b2e17
          | (have j0 := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e17 b2e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e198
        have b2e219 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have j0 := b2e216 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e216
        have b2e222 : ∀ X0 : G, y = (σ y) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e219 X0
             have i₂ := b2e36 X0
             grind)
          | exact superpose b2e36 b2e219
          | (have j0 := b2e219 X0
             grind)
          | exact resolve b2e219 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e219
        have b2e224 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e222 X0
             grind)
          | (have r₁ := b2e222 X0
             have r₂ := b2e45
             grind)
          | exact resolve b2e222 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e222
        have b2e360 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e224 (σ x)
             grind)
          | exact superpose b2e224 b2e22
          | (have r₁ := b2e22
             have r₂ := b2e224 (σ x)
             grind)
          | exact resolve b2e22 b2e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e224
        have b2e361 : False := by grind
        exact b2e361
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e25
          | exact resolve b3e25 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e26
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : x = (k x y) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e27
          | exact resolve b3e27 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e53 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e53
        have b3e60 : y = (k x y) := by
          first
          | (have r₁ := b3e59
             have r₂ := b3e20
             grind)
          | exact resolve b3e59 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e61 : x = y := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e60
          | exact resolve b3e60 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e60
        have b3e63 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e24
          | exact resolve b3e24 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e66 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e63
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e67 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e66
          | exact resolve b3e66 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e66
        have b3e68 : False := by grind
        exact b3e68
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ x) ≠ (σ x) := by
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X1 X0 x
               have i₂ := b5e13 X1 x X1
               grind)
            | (have i₁ := b5e31 X0 X1 (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e46 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e51 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e46
          have b5e52 : y = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e35 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e35 X0 (σ x)
               grind)
            | exact superpose b5e35 b5e23
            | exact resolve b5e23 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e140 : ∀ X0 X1 X2 : G, (σ y) ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e97 X1
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e97
            | exact resolve b5e97 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e825 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e826 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e825
               have r₂ := b5e24
               grind)
            | exact resolve b5e825 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e825
          have b5e827 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e826
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e826
            | exact resolve b5e826 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e826
          have b5e828 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e827
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e827
            | exact resolve b5e827 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e827
          have b5e840 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e140 X0 (σ x) (σ y)
               have i₂ := b5e828
               grind)
            | exact superpose b5e828 b5e140
            | exact resolve b5e140 b5e828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140
          have b5e1172 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e840 (σ x)
               have i₂ := b5e828
               grind)
            | exact superpose b5e828 b5e840
            | (have r₁ := b5e840 (σ x)
               have r₂ := b5e828
               grind)
            | exact resolve b5e840 b5e828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e828 b5e840
          have b5e1175 : False := by grind
          exact b5e1175
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e25
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : x = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e70 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e27
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e27 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e81 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e70
        have b6e87 : y = (M.op x x) := by
          first
          | (have r₁ := b6e81
             have r₂ := b6e21
             grind)
          | exact resolve b6e81 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e93 : False := by grind
        exact b6e93
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 X1 X0 x
               have i₂ := b7e13 X1 x X1
               grind)
            | (have i₁ := b7e31 X0 X1 (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e52 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e35 x X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e35 X0 x
               grind)
            | exact superpose b7e35 b7e21
            | exact resolve b7e21 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e58 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e63 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e58
          have b7e64 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e23
               grind)
            | exact resolve b7e63 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e65 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : ∀ X0 X1 X2 : G, y ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e52 X1
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e52
            | exact resolve b7e52 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e94 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e95 : y = (k x y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e101 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e102 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e101
               have r₂ := b7e21
               grind)
            | exact resolve b7e101 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e104 : y = (M.op x y) := by
            first
            | (have r₁ := b7e102
               have r₂ := b7e22
               grind)
            | exact resolve b7e102 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e387 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e68 X0 x y
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e68
            | exact resolve b7e68 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e457 : y ≠ y := by
            first
            | (have i₁ := b7e387 x
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e387
            | (have r₁ := b7e387 x
               have r₂ := b7e104
               grind)
            | exact resolve b7e387 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104 b7e387
          have b7e458 : False := by grind
          exact b7e458
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e91 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e818 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e91 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e818
               have r₂ := b8e24
               grind)
            | exact resolve b8e818 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e818
          have b8e820 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e819
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e819
            | exact resolve b8e819 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e819
          have b8e822 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e820
               grind)
            | exact superpose b8e820 b8e20
            | exact resolve b8e20 b8e820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e820
          have b8e1318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e822
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e822
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e822 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e822
          have b8e1319 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e1318
          have b8e1323 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1319
               have r₂ := b8e21
               grind)
            | exact resolve b8e1319 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1319
          have b8e1327 : False := by grind
          exact b8e1327

/-- `Equation314`: `x ◇ x = y ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation314 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law314 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law314.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 y x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e23 X0
           grind)
        | exact superpose b0e23 b0e11
        | exact resolve b0e11 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e36 X0 x
           have i₂ := b0e23 x
           grind)
        | exact superpose b0e23 b0e36
        | exact resolve b0e36 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e44 : y = (σ y) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e38 (σ y)
           grind)
        | exact superpose b0e38 b0e20
        | exact resolve b0e20 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e56 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e18
        | exact resolve b0e18 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e56
           have i₂ := b0e23 (σ x)
           grind)
        | exact superpose b0e23 b0e56
        | exact resolve b0e56 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e63 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e62
           have i₂ := b0e23 x
           grind)
        | exact superpose b0e23 b0e62
        | exact resolve b0e62 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e62
      have b0e64 : False := by grind
      exact b0e64
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 y x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e36 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e23
          | exact resolve b1e23 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e26
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e35 x
             grind)
          | exact superpose b1e35 b1e51
          | exact resolve b1e51 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e51
        have b1e54 : False := by grind
        exact b1e54
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 y x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e25 y
             grind)
          | exact resolve b2e15 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e36 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e46 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e152 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e46 X0 y
             have i₂ := b2e36 (τ X0)
             grind)
          | exact superpose b2e36 b2e46
          | exact resolve b2e46 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e46
        have b2e158 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e152 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e152
          | exact resolve b2e152 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e152
        have b2e162 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e17 X0 (σ y)
             have i₂ := b2e158 X0
             grind)
          | exact superpose b2e158 b2e17
          | (have j0 := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e17 b2e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e158
        have b2e164 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e162 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e162
        have b2e167 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e164 X0
             grind)
          | (have r₁ := b2e164 (σ y)
             have r₂ := b2e21
             grind)
          | (have r₁ := b2e164 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e164 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e164
        have b2e184 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e167 (σ x)
             grind)
          | exact superpose b2e167 b2e22
          | (have r₁ := b2e22
             have r₂ := b2e167 (σ x)
             grind)
          | exact resolve b2e22 b2e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e167
        have b2e194 : False := by grind
        exact b2e194
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) x (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e39 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e35 (σ X0)
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e45 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : y = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e52 : y = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e20
             grind)
          | exact resolve b3e50 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e68 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e27 (σ x)
             grind)
          | exact superpose b3e27 b3e23
          | exact resolve b3e23 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e27
        have b3e425 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e39 x
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e39
          | exact resolve b3e39 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e52
        have b3e438 : False := by grind
        exact b3e438
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X1 X3 X4
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X1 X0 x
               have i₂ := b5e13 X1 x X1
               grind)
            | (have i₁ := b5e30 X0 X1 (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b5e13 b5e30
            | exact resolve b5e30 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e34 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X2 (M.op X0 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X2 (M.op X0 X1)
               have i₂ := b5e13 X0 (M.op X0 X1) X1
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 X2 (M.op X0 X1)
               grind)
            | (have r₁ := b5e16 X0 (M.op X0 X0)
               have r₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e66 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e73 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e66
          have b5e75 : y = (k x y) := by
            first
            | (have r₁ := b5e73
               have r₂ := b5e21
               grind)
            | exact resolve b5e73 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e88 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e90 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e114 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e41 X1 X0
               grind)
            | exact superpose b5e41 b5e14
            | exact resolve b5e14 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e529 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e34 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e559 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 y
               have i₂ := b5e91 (σ X0)
               grind)
            | exact superpose b5e91 b5e19
            | (have j1 := b5e91 (σ X0)
               grind)
            | exact resolve b5e19 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e595 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op X2 (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e88 (σ X1) X2 (σ X0)
               grind)
            | exact superpose b5e88 b5e19
            | (have j1 := b5e88 (σ X1) X2 (σ X0)
               grind)
            | exact resolve b5e19 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e1213 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e82 X0 X0
               have i₂ := b5e32 (σ X0) X1
               grind)
            | (have i₁ := b5e82 X0 X0
               have i₂ := b5e32 X0 (σ X0)
               grind)
            | exact superpose b5e32 b5e82
            | exact resolve b5e82 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1237 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X1 (σ X0)
               have i₂ := b5e82 X0 X0
               grind)
            | exact superpose b5e82 b5e32
            | (have j1 := b5e82 X0 X0
               grind)
            | exact resolve b5e32 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e1250 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (σ X0) X3)) = (M.op X4 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e26 X2 (σ X0) X3 X4 (σ X1)
               have i₂ := b5e82 X0 X1
               grind)
            | exact superpose b5e82 b5e26
            | (have j1 := b5e82 X1 X1
               grind)
            | exact resolve b5e26 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e82
          have b5e1304 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e1237 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1237
          have b5e1315 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e1213 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1213
          have b5e1656 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e114 X0 (M.op X1 X1)
               have i₂ := b5e529 (σ X0) X1
               grind)
            | exact superpose b5e529 b5e114
            | exact resolve b5e114 b5e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e529
          have b5e1679 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1656 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1656
            | exact resolve b5e1656 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1656
          have b5e1719 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e114 X0 (τ (M.op X1 X1))
               have i₂ := b5e1679 (σ X0) X1
               grind)
            | exact superpose b5e1679 b5e114
            | exact resolve b5e114 b5e1679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e114 b5e1679
          have b5e1731 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1719 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1719
            | exact resolve b5e1719 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1719
          have b5e3116 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1315 X1 (τ (τ (M.op X0 X0)))
               have i₂ := b5e1731 (τ (τ (M.op X0 X0))) X0
               grind)
            | exact superpose b5e1731 b5e1315
            | (have j0 := b5e1315 X1 (τ (τ (M.op X0 X0)))
               grind)
            | exact resolve b5e1315 b5e1731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1315 b5e1731
          have b5e3213 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have j0 := b5e3116 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3116
          have b5e3267 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3213 X0 X1
               have i₂ := b5e15 (τ (M.op X0 X0))
               grind)
            | exact superpose b5e15 b5e3213
            | exact resolve b5e3213 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3213
          have b5e5417 : ∀ X0 : G, (σ y) ≠ (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e3267 X0 (σ y)
               grind)
            | exact superpose b5e3267 b5e23
            | exact resolve b5e23 b5e3267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6123 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ (k y y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e1304 y X0
               grind)
            | exact superpose b5e1304 b5e23
            | (have j1 := b5e1304 y X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e1304 y x
               grind)
            | exact resolve b5e23 b5e1304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1304
          have b5e6187 : ∀ X0 : G, (M.op X0 X0) = (σ (k y y)) := by
            intro X0
            first
            | (have j0 := b5e6123 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6123
          have b5e6957 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e3267 (σ y) X0
               have i₂ := b5e559 y
               grind)
            | exact superpose b5e559 b5e3267
            | (have j1 := b5e559 y
               grind)
            | exact resolve b5e3267 b5e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3267
          have b5e6964 : (σ y) ≠ (τ (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e5417 (σ y)
               have i₂ := b5e559 y
               grind)
            | exact superpose b5e559 b5e5417
            | (have j1 := b5e559 y
               grind)
            | exact resolve b5e5417 b5e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5417
          have b5e7003 : (σ y) ≠ (τ (σ (k y y))) := by
            first
            | (have r₁ := b5e6964
               have r₂ := b5e23
               grind)
            | exact resolve b5e6964 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6964
          have b5e7005 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (k y y))) := by
            intro X0
            first
            | (have j0 := b5e6957 X0
               grind)
            | (have r₁ := b5e6957 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e6957 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6957
          have b5e7016 : (σ y) ≠ (k y y) := by
            first
            | (have i₁ := b5e7003
               have i₂ := b5e14 (k y y)
               grind)
            | exact superpose b5e14 b5e7003
            | exact resolve b5e7003 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7003
          have b5e7018 : ∀ X0 : G, (M.op X0 X0) = (k y y) := by
            intro X0
            first
            | (have i₁ := b5e7005 X0
               have i₂ := b5e14 (k y y)
               grind)
            | exact superpose b5e14 b5e7005
            | exact resolve b5e7005 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7005
          have b5e8221 : (k y y) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e7018 (σ y)
               have i₂ := b5e559 y
               grind)
            | exact superpose b5e559 b5e7018
            | (have j1 := b5e559 y
               grind)
            | exact resolve b5e7018 b5e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e559 b5e7018
          have b5e8406 : (k y y) = (σ (k y y)) := by
            first
            | (have r₁ := b5e8221
               have r₂ := b5e23
               grind)
            | exact resolve b5e8221 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8221
          have b5e20225 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e595 X0 X1 (σ X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e595
          have b5e28700 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1250 x y X0 X1 X2
               have i₂ := b5e75
               grind)
            | exact superpose b5e75 b5e1250
            | (have j0 := b5e1250 y y X2 x x
               grind)
            | exact resolve b5e1250 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1250
          have b5e29480 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e28700 X0 X1 X2
               grind)
            | (have r₁ := b5e28700 X0 X1 X2
               have r₂ := b5e23
               grind)
            | exact resolve b5e28700 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28700
          have b5e29729 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e29480 X0 X1 X2
               grind)
            | (have r₁ := b5e29480 X0 X1 X2
               have r₂ := b5e24
               grind)
            | exact resolve b5e29480 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29480
          have b5e29887 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op X2 (σ y)) := by
            intro X2
            first
            | (have i₁ := b5e29729 x x X2
               have i₂ := b5e13 (σ x) x x
               grind)
            | (have i₁ := b5e29729 (M.op (σ x) x) x X2
               have i₂ := b5e13 (M.op (σ x) x) x X2
               grind)
            | exact superpose b5e13 b5e29729
            | exact resolve b5e29729 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29729
          have b5e29986 : ∀ X2 : G, (σ (k y y)) = (M.op X2 (σ y)) := by
            intro X2
            first
            | (have i₁ := b5e29887 X2
               have i₂ := b5e6187 (σ x)
               grind)
            | exact superpose b5e6187 b5e29887
            | exact resolve b5e29887 b5e6187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6187 b5e29887
          have b5e30030 : ∀ X2 : G, (k y y) = (M.op X2 (σ y)) := by
            intro X2
            first
            | (have i₁ := b5e29986 X2
               have i₂ := b5e8406
               grind)
            | exact superpose b5e8406 b5e29986
            | exact resolve b5e29986 b5e8406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8406 b5e29986
          have b5e315778 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e20225 x y
               have i₂ := b5e75
               grind)
            | exact superpose b5e75 b5e20225
            | (have j0 := b5e20225 x y
               grind)
            | exact resolve b5e20225 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75 b5e20225
          have b5e315974 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e315778
          have b5e315997 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e315974
               have r₂ := b5e24
               grind)
            | exact resolve b5e315974 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315974
          have b5e315998 : (σ y) = (k y y) := by
            first
            | (have i₁ := b5e315997
               have i₂ := b5e30030 (σ x)
               grind)
            | exact superpose b5e30030 b5e315997
            | exact resolve b5e315997 b5e30030
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30030 b5e315997
          have b5e315999 : False := by grind
          exact b5e315999
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e25 (σ y)
             grind)
          | exact superpose b6e25 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e25 (σ y)
             grind)
          | exact resolve b6e15 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e50 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e36 (σ X0)
             grind)
          | exact superpose b6e36 b6e18
          | exact resolve b6e18 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e140 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e50 X0
             grind)
          | exact superpose b6e50 b6e13
          | exact resolve b6e13 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e141 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e140 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e140
          | exact resolve b6e140 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e140
        have b6e158 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e17 X0 y
             have i₂ := b6e141 X0
             grind)
          | exact superpose b6e141 b6e17
          | (have j0 := b6e17 X0 y
             grind)
          | exact resolve b6e17 b6e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e160 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e158 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e163 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e160 X0
             grind)
          | (have r₁ := b6e160 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e160 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e160 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160
        have b6e274 : x ≠ x := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e163 x
             grind)
          | exact superpose b6e163 b6e21
          | (have r₁ := b6e21
             have r₂ := b6e163 x
             grind)
          | exact resolve b6e21 b6e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163
        have b6e285 : False := by grind
        exact b6e285
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e30 X1 X0 x
               have i₂ := b7e13 X1 x X1
               grind)
            | (have i₁ := b7e30 X0 X1 (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e50 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e32 y X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e32 X0 y
               grind)
            | exact superpose b7e32 b7e21
            | exact resolve b7e21 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e57 : ∀ X0 X1 X2 : G, y ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e50 X1
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e50
            | exact resolve b7e50 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e65 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e70 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e65
          have b7e72 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e23
               grind)
            | exact resolve b7e70 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e72
            | exact resolve b7e72 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e76 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e14
            | exact resolve b7e14 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e77 : y = (k x y) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e76
            | exact resolve b7e76 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e101 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e102 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e101
               have r₂ := b7e21
               grind)
            | exact resolve b7e101 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e104 : y = (M.op x y) := by
            first
            | (have r₁ := b7e102
               have r₂ := b7e22
               grind)
            | exact resolve b7e102 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e338 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e57 X0 x y
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e57
            | exact resolve b7e57 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e404 : y ≠ y := by
            first
            | (have i₁ := b7e338 x
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e338
            | (have r₁ := b7e338 x
               have r₂ := b7e104
               grind)
            | exact resolve b7e338 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104 b7e338
          have b7e405 : False := by grind
          exact b7e405
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e81 x y
               grind)
            | exact superpose b8e81 b8e20
            | (have j1 := b8e81 y y
               grind)
            | exact resolve b8e20 b8e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e1267 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1159
               have r₂ := b8e23
               grind)
            | exact resolve b8e1159 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1159
          have b8e1271 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1267
               have r₂ := b8e24
               grind)
            | exact resolve b8e1267 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1267
          have b8e1275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1271
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1271
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e1271 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1271
          have b8e1276 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e1275
          have b8e1279 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1276
               have r₂ := b8e21
               grind)
            | exact resolve b8e1276 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1276
          have b8e1282 : False := by grind
          exact b8e1282

/-- `Equation318`: `x ◇ x = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pxy_pxy_y_pxy_Equation318 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law318 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law318.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 : G, x = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e11 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) x (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e24 (σ x)
           grind)
        | exact superpose b0e24 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) x
           have r₂ := b0e24 (σ x)
           grind)
        | exact resolve b0e14 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e40 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e23 x
           grind)
        | exact superpose b0e23 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e23 x
           grind)
        | exact resolve b0e14 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e41 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have j0 := b0e40 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e42 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e54 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e42 (σ X0)
           grind)
        | exact superpose b0e42 b0e17
        | exact resolve b0e17 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e55 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e54
        | exact resolve b0e54 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e54
      have b0e2564 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e55 y
           grind)
        | exact superpose b0e55 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e55 y
           grind)
        | exact resolve b0e18 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e2601 : False := by grind
      exact b0e2601
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 (τ X0) X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X2) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 (M.op X1 X0) X2
             have i₂ := b1e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 (M.op X1 X0) X2
             grind)
          | (have r₁ := b1e15 (M.op X0 X0) X1
             have r₂ := b1e12 X0 (M.op X0 X0) X0
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e26 x
             grind)
          | exact resolve b1e15 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e60 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 x
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e16
          | (have j0 := b1e16 X0 x
             grind)
          | exact resolve b1e16 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e79 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (k X0 x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e17 X0 x
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e17
          | (have j0 := b1e17 X0 x
             grind)
          | exact resolve b1e17 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e94 : ∀ X0 : G, (M.op X0 X0) = x ∨ (M.op X0 x) = (k X0 x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e17 X0 x
             grind)
          | (have i₁ := b1e26 x
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e26
          | (have j1 := b1e17 X0 x
             grind)
          | exact resolve b1e26 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e95 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e99 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e95 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e95 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e95 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e95
        have b1e100 : ∀ X0 : G, (M.op X0 X0) = x ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e94 X0
             have j1 := b1e15 X0 x
             grind)
          | (have r₁ := b1e94 x
             have r₂ := b1e15 x x
             grind)
          | (have r₁ := b1e94 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e94 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94
        have b1e112 : ∀ X0 : G, x = (k X0 x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e79 X0
             have j1 := b1e60 X0
             grind)
          | (have r₁ := b1e79 X0
             have r₂ := b1e60 X0
             grind)
          | (have r₁ := b1e79 x
             have r₂ := b1e60 x
             grind)
          | exact resolve b1e79 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e79
        have b1e116 : ∀ X0 : G, x = (k X0 x) ∨ (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b1e100 X0
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e100
          | (have j0 := b1e100 X0
             grind)
          | exact resolve b1e100 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100
        have b1e525 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e99 X0 x
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e99
          | (have r₁ := b1e99 x x
             have r₂ := b1e26 x
             grind)
          | exact resolve b1e99 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e99
        have b1e1251 : ∀ X0 : G, x = X0 ∨ x = (k X0 x) ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e112 X0
             have i₂ := b1e116 X0
             grind)
          | exact superpose b1e116 b1e112
          | (have j0 := b1e112 X0
             have j1 := b1e116 X0
             grind)
          | exact resolve b1e112 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112 b1e116
        have b1e1281 : ∀ X0 : G, x = X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e1251 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1251
        have b1e1293 : ∀ X0 : G, x = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e1281 (k X0 x)
             have j1 := b1e525 X0
             grind)
          | (have r₁ := b1e1281 X0
             have r₂ := b1e525 X0
             grind)
          | (have r₁ := b1e1281 x
             have r₂ := b1e525 x
             grind)
          | (have r₁ := b1e1281 X0
             have r₂ := b1e525 (k X0 x)
             grind)
          | exact resolve b1e1281 b1e525
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e525 b1e1281
        have b1e1347 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e31 X0 x
             have i₂ := b1e1293 (τ X0)
             grind)
          | exact superpose b1e1293 b1e31
          | exact resolve b1e31 b1e1293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e1293
        have b1e1398 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have j0 := b1e51 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e1736 : (σ x) = (M.op x (σ x)) := by
          first
          | (have i₁ := b1e53 (σ x)
             have i₂ := b1e1347 x
             grind)
          | exact superpose b1e1347 b1e53
          | exact resolve b1e53 b1e1347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e1829 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) X0 x
             have i₂ := b1e1736
             grind)
          | exact superpose b1e1736 b1e12
          | exact resolve b1e12 b1e1736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1736
        have b1e4068 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e1347 (M.op X0 X0)
             have i₂ := b1e1398 X0 (σ x)
             grind)
          | exact superpose b1e1398 b1e1347
          | exact resolve b1e1347 b1e1398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1347 b1e1398
        have b1e4078 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e4068 x
             have i₂ := b1e1829 (M.op x x)
             grind)
          | exact superpose b1e1829 b1e4068
          | exact resolve b1e4068 b1e1829
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1829 b1e4068
        have b1e4085 : False := by grind
        exact b1e4085
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e25 x
             grind)
          | exact resolve b2e15 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e50 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b2e49 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
        have b2e3471 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e77 x y
             grind)
          | exact superpose b2e77 b2e22
          | (have j1 := b2e77 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e77 x y
             grind)
          | exact resolve b2e22 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e3531 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e3471
        have b2e3567 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e3531
             have r₂ := b2e21
             grind)
          | exact resolve b2e3531 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3531
        have b2e3658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e3567
             have i₂ := b2e50 y
             grind)
          | exact superpose b2e50 b2e3567
          | exact resolve b2e3567 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e3567
        have b2e3722 : False := by grind
        exact b2e3722
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) x (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e45 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X0
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e82 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e88 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e87 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e88 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e88 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e88 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e36 X1 X0
             grind)
          | exact superpose b3e36 b3e13
          | exact resolve b3e13 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e453 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e94 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e588 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e453 X0 (σ x)
             have i₂ := b3e27 X0
             grind)
          | exact superpose b3e27 b3e453
          | (have j0 := b3e453 X0 (σ x)
             grind)
          | (have r₁ := b3e453 X0 (σ x)
             have r₂ := b3e27 X0
             grind)
          | exact resolve b3e453 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e453
        have b3e594 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e588 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e588
        have b3e864 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e117 X0 (σ x)
             have i₂ := b3e594 (σ X0)
             grind)
          | exact superpose b3e594 b3e117
          | exact resolve b3e117 b3e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117 b3e594
        have b3e866 : ∀ X0 : G, x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e864 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e864
          | exact resolve b3e864 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e864
        have b3e1039 : x = (M.op (σ x) x) := by
          first
          | (have i₁ := b3e47 x
             have i₂ := b3e866 (σ x)
             grind)
          | exact superpose b3e866 b3e47
          | exact resolve b3e47 b3e866
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e866
        have b3e1100 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 (σ x)
             have i₂ := b3e1039
             grind)
          | exact superpose b3e1039 b3e12
          | exact resolve b3e12 b3e1039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3539 : x = (M.op x x) := by
          first
          | (have i₁ := b3e1039
             have i₂ := b3e1100 (σ x)
             grind)
          | exact superpose b3e1100 b3e1039
          | exact resolve b3e1039 b3e1100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1039 b3e1100
        have b3e3543 : False := by grind
        exact b3e3543
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X2 X3 X4
               have i₂ := b4e13 X2 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op X3 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X2 X3) X2
               have i₂ := b4e13 (M.op X2 X3) X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e37 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e45 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X2) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 (M.op X1 X0) X2
               have i₂ := b4e13 X0 (M.op X1 X0) X1
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X1 X0) X2
               grind)
            | (have r₁ := b4e16 (M.op X0 X0) X1
               have r₂ := b4e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e37 X1 X0
               grind)
            | exact superpose b4e37 b4e14
            | exact resolve b4e14 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e94 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e93 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e94 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e94 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e94 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e139 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X6 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b4e27 X3 X4 (M.op X5 X2) X6 x
               have i₂ := b4e27 x X5 X2 X0 X1
               grind)
            | (have i₁ := b4e27 X3 X4 (M.op X5 X2) X6 x
               have i₂ := b4e27 X0 X1 X2 x X5
               grind)
            | exact superpose b4e27 b4e27
            | exact resolve b4e27 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e241 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X2 X0)) ∨ (M.op (M.op X1 (M.op X2 X0)) X3) = (k (M.op X1 (M.op X2 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16 (M.op X1 (M.op X2 X0)) X3
               have i₂ := b4e32 (M.op X1 (M.op X2 X0)) X1 X2 X0
               grind)
            | exact superpose b4e32 b4e16
            | (have j0 := b4e16 (M.op X1 (M.op X2 X0)) X3
               grind)
            | exact resolve b4e16 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e272 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (k (M.op X1 (M.op X2 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e241 X0 X1 X2 X3
               grind)
            | (have r₁ := b4e241 X0 X1 X2 X3
               have r₂ := b4e13 X0 X1 X2
               grind)
            | exact resolve b4e241 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e241
          have b4e455 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e99 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e503 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op X2 (M.op X3 X0)) ∨ (M.op X2 (M.op X3 X0)) = (k X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e455 X1 (M.op X2 (M.op X3 X0))
               have i₂ := b4e32 X1 X2 X3 X0
               grind)
            | exact superpose b4e32 b4e455
            | (have j0 := b4e455 X1 (M.op X2 (M.op X3 X0))
               grind)
            | exact resolve b4e455 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e455
          have b4e512 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (k X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e503 X0 X1 X2 X3
               grind)
            | (have r₁ := b4e503 X0 X1 X1 X2
               have r₂ := b4e13 X0 X1 X2
               grind)
            | exact resolve b4e503 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e503
          have b4e1132 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e45 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e1176 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 X1 (M.op X0 X0)
               have i₂ := b4e1132 X0 (τ X1)
               grind)
            | exact superpose b4e1132 b4e37
            | exact resolve b4e37 b4e1132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e3025 : ∀ X0 X4 : G, (M.op X0 X0) = (k X4 (M.op X0 X0)) := by
            intro X0 X4
            first
            | (have i₁ := b4e512 (M.op x x) x X0 x
               have i₂ := b4e32 X0 x x x
               grind)
            | exact superpose b4e32 b4e512
            | exact resolve b4e512 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e512
          have b4e3432 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e52 X1 (M.op X0 X0)
               have i₂ := b4e3025 X0 (σ X1)
               grind)
            | exact superpose b4e3025 b4e52
            | exact resolve b4e52 b4e3025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3433 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X1 (M.op X0 X0)
               have i₂ := b4e3025 X0 (τ X1)
               grind)
            | exact superpose b4e3025 b4e36
            | exact resolve b4e36 b4e3025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3561 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op X1 X1) (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1132 X1 (τ (M.op X0 X0))
               have i₂ := b4e3432 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e3432 b4e1132
            | exact resolve b4e1132 b4e3432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3432
          have b4e3847 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1132 X1 (σ (M.op X0 X0))
               have i₂ := b4e3433 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e3433 b4e1132
            | exact resolve b4e1132 b4e3433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3851 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X1 (σ (M.op X0 X0))
               have i₂ := b4e3433 X0 (τ X1)
               grind)
            | exact superpose b4e3433 b4e36
            | exact resolve b4e36 b4e3433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e3433
          have b4e4078 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (τ (M.op X0 X0)))) = (M.op X3 (τ (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e27 X1 X2 (τ (M.op X0 X0)) X3 (M.op x x)
               have i₂ := b4e3561 X0 x
               grind)
            | exact superpose b4e3561 b4e27
            | exact resolve b4e27 b4e3561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e4079 : ∀ X0 X1 X3 : G, (M.op X1 (τ (M.op X0 X0))) = (M.op X3 (M.op X1 (τ (M.op X0 X0)))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e30 X0 (M.op X1 X1) (τ (M.op X0 X0)) X3
               have i₂ := b4e3561 X0 X1
               grind)
            | exact superpose b4e3561 b4e30
            | exact resolve b4e30 b4e3561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4597 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 X3) (σ (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e3847 (M.op X0 (M.op X1 X2)) X1
               have i₂ := b4e30 X0 X1 X2 (M.op X0 (M.op X1 X2))
               grind)
            | exact superpose b4e30 b4e3847
            | exact resolve b4e3847 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3847
          have b4e4776 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (M.op X1 X1) (σ (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1132 X1 (σ (σ (M.op X0 X0)))
               have i₂ := b4e3851 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e3851 b4e1132
            | exact resolve b4e1132 b4e3851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3851
          have b4e8210 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (M.op X0 X0))) X3) = (k (M.op X1 (τ (M.op X0 X0))) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e272 (τ (M.op X0 X0)) X1 (M.op X1 X1) X3
               have i₂ := b4e3561 X0 X1
               grind)
            | exact superpose b4e3561 b4e272
            | exact resolve b4e272 b4e3561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272 b4e3561
          have b4e15814 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 (τ (M.op X2 X2))))) = (k (σ (M.op X3 X3)) (M.op X2 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e1176 X3 (M.op X2 X2)
               have i₂ := b4e4078 X2 X0 X1 (M.op X3 X3)
               grind)
            | exact superpose b4e4078 b4e1176
            | exact resolve b4e1176 b4e4078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1176 b4e4078
          have b4e15822 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op X0 (M.op X1 (τ (M.op X2 X2))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e15814 X0 X1 X2 x
               have i₂ := b4e3025 X2 (σ (M.op x x))
               grind)
            | exact superpose b4e3025 b4e15814
            | exact resolve b4e15814 b4e3025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3025 b4e15814
          have b4e15937 : ∀ X1 X2 : G, (M.op X2 X2) = (σ (M.op X1 (τ (M.op X2 X2)))) := by
            intro X1 X2
            first
            | (have i₁ := b4e15822 x X1 X2
               have i₂ := b4e4079 X2 X1 x
               grind)
            | exact superpose b4e4079 b4e15822
            | exact resolve b4e15822 b4e4079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4079 b4e15822
          have b4e16400 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (M.op X1 (τ (M.op X0 X0)))
               have i₂ := b4e15937 X1 X0
               grind)
            | exact superpose b4e15937 b4e14
            | exact resolve b4e14 b4e15937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e16401 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (σ X2)) = (σ (k (M.op X1 (τ (M.op X0 X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 (M.op X1 (τ (M.op X0 X0))) X2
               have i₂ := b4e15937 X1 X0
               grind)
            | exact superpose b4e15937 b4e19
            | exact resolve b4e19 b4e15937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e16412 : ∀ X0 X1 X2 : G, (τ (k (M.op X0 X0) X2)) = (k (M.op X1 (τ (M.op X0 X0))) (τ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e52 (M.op X1 (τ (M.op X0 X0))) X2
               have i₂ := b4e15937 X1 X0
               grind)
            | exact superpose b4e15937 b4e52
            | exact resolve b4e52 b4e15937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e16440 : ∀ X0 X1 X2 : G, (τ (k (M.op X0 X0) X2)) = (M.op (M.op X1 (τ (M.op X0 X0))) (τ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16412 X0 X1 X2
               have i₂ := b4e8210 X0 X1 (τ X2)
               grind)
            | exact superpose b4e8210 b4e16412
            | exact resolve b4e16412 b4e8210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16412
          have b4e16451 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (σ X2)) = (σ (M.op (M.op X1 (τ (M.op X0 X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16401 X0 X1 X2
               have i₂ := b4e8210 X0 X1 X2
               grind)
            | exact superpose b4e8210 b4e16401
            | exact resolve b4e16401 b4e8210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8210 b4e16401
          have b4e16484 : ∀ X0 X2 : G, (τ (k (M.op X0 X0) X2)) = (M.op (τ (M.op X0 X0)) (τ X2)) := by
            intro X0 X2
            first
            | (have i₁ := b4e16440 X0 x X2
               have i₂ := b4e16400 X0 x
               grind)
            | exact superpose b4e16400 b4e16440
            | exact resolve b4e16440 b4e16400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16440
          have b4e16495 : ∀ X0 X2 : G, (k (M.op X0 X0) (σ X2)) = (σ (M.op (τ (M.op X0 X0)) X2)) := by
            intro X0 X2
            first
            | (have i₁ := b4e16451 X0 x X2
               have i₂ := b4e16400 X0 x
               grind)
            | exact superpose b4e16400 b4e16451
            | exact resolve b4e16451 b4e16400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16451
          have b4e16506 : ∀ X0 X2 : G, (τ (M.op (M.op X0 X0) X2)) = (M.op (τ (M.op X0 X0)) (τ X2)) := by
            intro X0 X2
            first
            | (have i₁ := b4e16484 X0 X2
               have i₂ := b4e1132 X0 X2
               grind)
            | exact superpose b4e1132 b4e16484
            | exact resolve b4e16484 b4e1132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16484
          have b4e16513 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (σ X2)) = (σ (M.op (τ (M.op X0 X0)) X2)) := by
            intro X0 X2
            first
            | (have i₁ := b4e16495 X0 X2
               have i₂ := b4e1132 X0 (σ X2)
               grind)
            | exact superpose b4e1132 b4e16495
            | exact resolve b4e16495 b4e1132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1132 b4e16495
          have b4e16672 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 (M.op X1 X2))) = (M.op X3 (τ (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16400 (M.op X0 (M.op X1 X2)) X1
               have i₂ := b4e30 X0 X1 X2 (M.op X0 (M.op X1 X2))
               grind)
            | exact superpose b4e30 b4e16400
            | exact resolve b4e16400 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16400
          have b4e20692 : ∀ X0 X1 X2 : G, (M.op (τ X1) (τ X1)) = (M.op X2 (τ (M.op (M.op X0 X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (τ X1) X2 (τ (M.op X0 X0))
               have i₂ := b4e16506 X0 X1
               grind)
            | exact superpose b4e16506 b4e13
            | exact resolve b4e13 b4e16506
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16506
          have b4e21065 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (σ (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16513 X1 (M.op X2 X0)
               have i₂ := b4e13 X0 (τ (M.op X1 X1)) X2
               grind)
            | exact superpose b4e13 b4e16513
            | exact resolve b4e16513 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e21545 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 X0)) = (M.op (M.op X3 X3) (σ (M.op X4 (M.op X1 (M.op X2 X0))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e21065 (M.op X1 (M.op X2 X0)) X3 X4
               have i₂ := b4e32 (M.op X1 (M.op X2 X0)) X1 X2 X0
               grind)
            | exact superpose b4e32 b4e21065
            | exact resolve b4e21065 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e21709 : ∀ X0 X1 X2 : G, (σ (M.op (σ (M.op X1 X0)) (σ (M.op X1 X0)))) = (M.op (M.op X2 X2) (σ (σ (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e21065 (σ (M.op X1 X0)) X2 (M.op x x)
               have i₂ := b4e21065 X0 x X1
               grind)
            | exact superpose b4e21065 b4e21065
            | exact resolve b4e21065 b4e21065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e21906 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (M.op (σ (M.op X1 X0)) (σ (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e21709 X0 X1 x
               have i₂ := b4e4776 X0 x
               grind)
            | exact superpose b4e4776 b4e21709
            | exact resolve b4e21709 b4e4776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4776 b4e21709
          have b4e21948 : ∀ X0 X1 X2 X4 : G, (σ (M.op X0 X0)) = (σ (M.op X4 (M.op X1 (M.op X2 X0)))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e21545 X0 X1 X2 x X4
               have i₂ := b4e4597 X4 X1 (M.op X2 X0) x
               grind)
            | exact superpose b4e4597 b4e21545
            | exact resolve b4e21545 b4e4597
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4597 b4e21545
          have b4e22010 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e21948 X0 X1 X2 x
               have i₂ := b4e30 X1 X2 X0 x
               grind)
            | exact superpose b4e30 b4e21948
            | exact resolve b4e21948 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21948
          have b4e22241 : ∀ X0 X1 X2 : G, (σ (M.op (σ (M.op X1 X0)) (σ (M.op X1 X0)))) = (σ (M.op X2 (σ (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e22010 (σ (M.op X1 X0)) X2 (M.op x x)
               have i₂ := b4e21065 X0 x X1
               grind)
            | exact superpose b4e21065 b4e22010
            | exact resolve b4e22010 b4e21065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e22489 : ∀ X0 X2 : G, (σ (σ (M.op X0 X0))) = (σ (M.op X2 (σ (M.op X0 X0)))) := by
            intro X0 X2
            first
            | (have i₁ := b4e22241 X0 x X2
               have i₂ := b4e21906 X0 x
               grind)
            | exact superpose b4e21906 b4e22241
            | exact resolve b4e22241 b4e21906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21906 b4e22241
          have b4e25059 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (τ (σ (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (M.op X1 (σ (M.op X0 X0)))
               have i₂ := b4e22489 X0 X1
               grind)
            | exact superpose b4e22489 b4e14
            | exact resolve b4e14 b4e22489
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22489
          have b4e25120 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e25059 X0 X1
               have i₂ := b4e14 (σ (M.op X0 X0))
               grind)
            | exact superpose b4e14 b4e25059
            | exact resolve b4e25059 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25059
          have b4e31202 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 (τ (M.op X0 (M.op X1 (M.op X2 X3))))) = (M.op (τ (M.op X4 (M.op X5 X3))) (τ (M.op X4 (M.op X5 X3)))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b4e20692 x (M.op X4 (M.op X5 X3)) X6
               have i₂ := b4e139 X1 X2 X3 (M.op x x) X4 X5 X0
               grind)
            | (have i₁ := b4e20692 x (M.op X4 (M.op X5 X3)) X6
               have i₂ := b4e139 X4 X5 X3 X0 X1 X2 (M.op x x)
               grind)
            | exact superpose b4e139 b4e20692
            | exact resolve b4e20692 b4e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139 b4e20692
          have b4e31726 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (τ (M.op X4 (M.op X5 X3))) = (M.op X6 (τ (M.op X0 (M.op X1 (M.op X2 X3))))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b4e31202 X0 X1 X2 X3 X4 X5 X6
               have i₂ := b4e16672 X4 X5 X3 (τ (M.op X4 (M.op X5 X3)))
               grind)
            | exact superpose b4e16672 b4e31202
            | exact resolve b4e31202 b4e16672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31202
          have b4e31808 : ∀ X0 X1 X2 X3 X4 X5 : G, (τ (M.op X0 (M.op X1 (M.op X2 X3)))) = (τ (M.op X4 (M.op X5 X3))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e31726 X0 X1 X2 X3 X4 X5 x
               have i₂ := b4e16672 X0 X1 (M.op X2 X3) x
               grind)
            | exact superpose b4e16672 b4e31726
            | exact resolve b4e31726 b4e16672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16672 b4e31726
          have b4e31836 : ∀ X1 X2 X3 X4 X5 : G, (τ (M.op X1 (M.op X2 X3))) = (τ (M.op X4 (M.op X5 X3))) := by
            intro X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e31808 x X1 X2 X3 X4 X5
               have i₂ := b4e30 X1 X2 X3 x
               grind)
            | exact superpose b4e30 b4e31808
            | exact resolve b4e31808 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31808
          have b4e35790 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op X1 (M.op X2 (σ (M.op X3 X0))))) = (τ (M.op X4 (σ (M.op X0 X0)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e31836 X1 X2 (σ (M.op X3 X0)) X4 (M.op x x)
               have i₂ := b4e21065 X0 x X3
               grind)
            | exact superpose b4e21065 b4e31836
            | exact resolve b4e31836 b4e21065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21065 b4e31836
          have b4e36034 : ∀ X0 X1 X2 X3 : G, (τ (σ (M.op X0 X0))) = (τ (M.op X1 (M.op X2 (σ (M.op X3 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35790 X0 X1 X2 X3 x
               have i₂ := b4e25120 X0 x
               grind)
            | exact superpose b4e25120 b4e35790
            | exact resolve b4e35790 b4e25120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25120 b4e35790
          have b4e36197 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (τ (M.op X1 (M.op X2 (σ (M.op X3 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e36034 X0 X1 X2 X3
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e36034
            | exact resolve b4e36034 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36034
          have b4e38824 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (τ (M.op X2 (M.op X3 (M.op (M.op X0 X0) (σ X1))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e36197 X1 X2 X3 (τ (M.op X0 X0))
               have i₂ := b4e16513 X0 X1
               grind)
            | exact superpose b4e16513 b4e36197
            | exact resolve b4e36197 b4e16513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16513 b4e36197
          have b4e39457 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (τ (M.op X3 (M.op (M.op X0 X0) (σ X1)))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e38824 X0 X1 x X3
               have i₂ := b4e30 X3 (M.op X0 X0) (σ X1) x
               grind)
            | exact superpose b4e30 b4e38824
            | exact resolve b4e38824 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e38824
          have b4e43624 : ∀ X0 X1 X2 : G, (σ (M.op X2 (M.op X0 X0))) = (M.op (M.op (M.op X1 X1) (σ X0)) (M.op (M.op X1 X1) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e15937 X2 (M.op (M.op X1 X1) (σ X0))
               have i₂ := b4e39457 X1 X0 (M.op (M.op X1 X1) (σ X0))
               grind)
            | exact superpose b4e39457 b4e15937
            | exact resolve b4e15937 b4e39457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15937 b4e39457
          have b4e43679 : ∀ X0 X2 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X2 (M.op X0 X0))) := by
            intro X0 X2
            first
            | (have i₁ := b4e43624 X0 x X2
               have i₂ := b4e13 (σ X0) (M.op (M.op x x) (σ X0)) (M.op x x)
               grind)
            | (have i₁ := b4e43624 X0 x X2
               have i₂ := b4e13 (M.op (M.op x x) (σ X0)) x X2
               grind)
            | exact superpose b4e13 b4e43624
            | exact resolve b4e43624 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43624
          have b4e43885 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e43679 X0 x
               have i₂ := b4e22010 X0 x X0
               grind)
            | (have i₁ := b4e43679 X0 (M.op X0 X0)
               have i₂ := b4e22010 (M.op X0 X0) x x
               grind)
            | exact superpose b4e22010 b4e43679
            | exact resolve b4e43679 b4e22010
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22010 b4e43679
          have b4e44577 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e43885 x
               grind)
            | exact superpose b4e43885 b4e26
            | (have r₁ := b4e26
               have r₂ := b4e43885 x
               grind)
            | exact resolve b4e26 b4e43885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e43885
          have b4e44776 : False := by grind
          exact b4e44776
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x x)) := by
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
          have b5e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op X3 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X2 X3) X2
               have i₂ := b5e13 (M.op X2 X3) X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b5e28 x
               have i₂ := b5e13 x x x
               grind)
            | (have i₁ := b5e28 (M.op x x)
               have i₂ := b5e13 (M.op x x) x x
               grind)
            | exact superpose b5e13 b5e28
            | exact resolve b5e28 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e42 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X2) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 (M.op X1 X0) X2
               have i₂ := b5e13 X0 (M.op X1 X0) X1
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 (M.op X1 X0) X2
               grind)
            | (have r₁ := b5e16 (M.op X0 X0) X1
               have r₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e36 X1 X0
               grind)
            | exact superpose b5e36 b5e14
            | exact resolve b5e14 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e55 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ y = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : x = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e55
          have b5e63 : y = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e21
               grind)
            | exact resolve b5e62 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
          have b5e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X0
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e86 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e85 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e86 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e86 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e86 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e409 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e421 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op X2 (M.op X3 X0)) ∨ (M.op X2 (M.op X3 X0)) = (k X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e409 X1 (M.op X2 (M.op X3 X0))
               have i₂ := b5e31 X1 X2 X3 X0
               grind)
            | exact superpose b5e31 b5e409
            | (have j0 := b5e409 X1 (M.op X2 (M.op X3 X0))
               grind)
            | exact resolve b5e409 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e409
          have b5e425 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (k X1 (M.op X2 (M.op X3 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e421 X0 X1 X2 X3
               grind)
            | (have r₁ := b5e421 X0 X1 X1 X2
               have r₂ := b5e13 X0 X1 X2
               grind)
            | exact resolve b5e421 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e421
          have b5e1014 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b5e42 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e2777 : ∀ X0 X4 : G, (M.op X0 X0) = (k X4 (M.op X0 X0)) := by
            intro X0 X4
            first
            | (have i₁ := b5e425 (M.op x x) x X0 x
               have i₂ := b5e31 X0 x x x
               grind)
            | exact superpose b5e31 b5e425
            | exact resolve b5e425 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e425
          have b5e3175 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e49 X1 (M.op X0 X0)
               have i₂ := b5e2777 X0 (σ X1)
               grind)
            | exact superpose b5e2777 b5e49
            | exact resolve b5e49 b5e2777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e2777
          have b5e3345 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e71 x y
               grind)
            | exact superpose b5e71 b5e24
            | (have j1 := b5e71 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e71 x y
               grind)
            | exact resolve b5e24 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e3468 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e3345
          have b5e3511 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e3468
               have r₂ := b5e23
               grind)
            | exact resolve b5e3468 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3468
          have b5e3528 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e3511
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e3511
            | exact resolve b5e3511 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e3511
          have b5e3535 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e25
               have i₂ := b5e3528
               grind)
            | exact superpose b5e3528 b5e25
            | exact resolve b5e25 b5e3528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
          have b5e3538 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e13 (σ y) X0 (σ x)
               have i₂ := b5e3528
               grind)
            | exact superpose b5e3528 b5e13
            | exact resolve b5e13 b5e3528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4109 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3538 X1
               have i₂ := b5e3538 X0
               grind)
            | (have i₁ := b5e3538 X0
               have i₂ := b5e3538 (σ y)
               grind)
            | exact superpose b5e3538 b5e3538
            | exact resolve b5e3538 b5e3538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4610 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e3528
               have i₂ := b5e4109 (σ x) X0
               grind)
            | (have i₁ := b5e3528
               have i₂ := b5e4109 X0 (σ x)
               grind)
            | exact superpose b5e4109 b5e3528
            | exact resolve b5e3528 b5e4109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3528 b5e4109
          have b5e4967 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e3175 (σ y) x
               have i₂ := b5e4610 (σ y)
               grind)
            | exact superpose b5e4610 b5e3175
            | exact resolve b5e3175 b5e4610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3175 b5e4610
          have b5e5011 : ∀ X0 : G, y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e4967 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e4967
            | exact resolve b5e4967 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4967
          have b5e5283 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b5e1014 X0 y
               have i₂ := b5e5011 (M.op X0 X0)
               grind)
            | exact superpose b5e5011 b5e1014
            | exact resolve b5e1014 b5e5011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1014 b5e5011
          have b5e5642 : ∀ X0 : G, y = (M.op (M.op X0 (σ y)) y) := by
            intro X0
            first
            | (have i₁ := b5e5283 (σ y)
               have i₂ := b5e3538 X0
               grind)
            | (have i₁ := b5e5283 (σ y)
               have i₂ := b5e3538 (σ y)
               grind)
            | exact superpose b5e3538 b5e5283
            | exact resolve b5e5283 b5e3538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3538
          have b5e5649 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 (M.op x x)
               have i₂ := b5e5283 x
               grind)
            | exact superpose b5e5283 b5e13
            | exact resolve b5e13 b5e5283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5283
          have b5e5681 : y = (M.op y y) := by
            first
            | (have i₁ := b5e5642 x
               have i₂ := b5e5649 (M.op x (σ y))
               grind)
            | exact superpose b5e5649 b5e5642
            | exact resolve b5e5642 b5e5649
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5642 b5e5649
          have b5e5771 : y = (M.op x x) := by
            first
            | (have i₁ := b5e33
               have i₂ := b5e5681
               grind)
            | exact superpose b5e5681 b5e33
            | exact resolve b5e33 b5e5681
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e5681
          have b5e5938 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e3535
               have i₂ := b5e5771
               grind)
            | exact superpose b5e5771 b5e3535
            | exact resolve b5e3535 b5e5771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3535 b5e5771
          have b5e5985 : False := by grind
          exact b5e5985
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) x (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e25 (σ x)
             grind)
          | exact superpose b6e25 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e25 (σ x)
             grind)
          | exact resolve b6e15 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e38 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e41 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e38 (σ X0)
             grind)
          | exact superpose b6e38 b6e18
          | exact resolve b6e18 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e320 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e41 y
             grind)
          | exact superpose b6e41 b6e19
          | exact resolve b6e19 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e320
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e320
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e320 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e320
        have b6e443 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e442
        have b6e445 : x = (M.op x x) := by
          first
          | (have r₁ := b6e443
             have r₂ := b6e21
             grind)
          | exact resolve b6e443 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e443
        have b6e446 : False := by grind
        exact b6e446
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e38 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e38 x
               have i₂ := b7e13 (σ x) x (σ x)
               grind)
            | (have i₁ := b7e38 (M.op (σ x) (σ x))
               have i₂ := b7e13 (M.op (σ x) (σ x)) x x
               grind)
            | exact superpose b7e13 b7e38
            | exact resolve b7e38 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e49 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X2) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 (M.op X1 X0) X2
               have i₂ := b7e13 X0 (M.op X1 X0) X1
               grind)
            | exact superpose b7e13 b7e16
            | (have j0 := b7e16 (M.op X1 X0) X2
               grind)
            | (have r₁ := b7e16 (M.op X0 X0) X1
               have r₂ := b7e13 X0 (M.op X0 X0) X0
               grind)
            | exact resolve b7e16 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e62
          have b7e66 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e23
               grind)
            | exact resolve b7e64 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e67 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e71 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : y = (k x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e71
            | exact resolve b7e71 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e85 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e67
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e67 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e17 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e17 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X0 X0
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e94 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e99 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e98 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e104 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e99 X0 X1
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e99 X0 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e99 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e112 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e22
               grind)
            | exact resolve b7e85 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e118 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e112
               have r₂ := b7e21
               grind)
            | exact resolve b7e112 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e121 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e122 : y = (M.op x y) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b7e121
               have r₂ := b7e22
               grind)
            | exact resolve b7e121 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e121
          have b7e124 : y = (M.op x y) := by
            first
            | (have r₁ := b7e122
               have r₂ := b7e21
               grind)
            | exact resolve b7e122 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122
          have b7e136 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e124
               grind)
            | exact superpose b7e124 b7e13
            | exact resolve b7e13 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e325 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e136 X1
               have i₂ := b7e136 X0
               grind)
            | (have i₁ := b7e136 X0
               have i₂ := b7e136 y
               grind)
            | exact superpose b7e136 b7e136
            | exact resolve b7e136 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e450 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e124
               have i₂ := b7e325 x X0
               grind)
            | (have i₁ := b7e124
               have i₂ := b7e325 X0 x
               grind)
            | exact superpose b7e325 b7e124
            | exact resolve b7e124 b7e325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124 b7e325
          have b7e504 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e104 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e515 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e16 y X0
               have i₂ := b7e450 y
               grind)
            | exact superpose b7e450 b7e16
            | (have j0 := b7e16 y X0
               grind)
            | (have r₁ := b7e16 y x
               have r₂ := b7e450 y
               grind)
            | exact resolve b7e16 b7e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e526 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b7e515 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e515
          have b7e1068 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b7e504 X0 y
               have i₂ := b7e450 X0
               grind)
            | exact superpose b7e450 b7e504
            | (have j0 := b7e504 X0 y
               grind)
            | (have r₁ := b7e504 X0 y
               have r₂ := b7e450 X0
               grind)
            | exact resolve b7e504 b7e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e450 b7e504
          have b7e1077 : ∀ X0 : G, y = (k X0 y) := by
            intro X0
            first
            | (have j0 := b7e1068 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1068
          have b7e1132 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b7e49 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e1422 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e32 X0 y
               have i₂ := b7e1077 (τ X0)
               grind)
            | exact superpose b7e1077 b7e32
            | exact resolve b7e32 b7e1077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e1077
          have b7e1558 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b7e526 (σ y)
               have i₂ := b7e1422 y
               grind)
            | exact superpose b7e1422 b7e526
            | exact resolve b7e526 b7e1422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e526
          have b7e1894 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) X0 y
               have i₂ := b7e1558
               grind)
            | exact superpose b7e1558 b7e13
            | exact resolve b7e13 b7e1558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1558
          have b7e3246 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e1422 (M.op X0 X0)
               have i₂ := b7e1132 X0 (σ y)
               grind)
            | exact superpose b7e1132 b7e1422
            | exact resolve b7e1422 b7e1132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1132 b7e1422
          have b7e3255 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e3246 x
               have i₂ := b7e1894 (M.op x x)
               grind)
            | exact superpose b7e1894 b7e3246
            | exact resolve b7e3246 b7e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1894 b7e3246
          have b7e3676 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e3255
               grind)
            | exact superpose b7e3255 b7e39
            | exact resolve b7e39 b7e3255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e3255
          have b7e3922 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e25
               have i₂ := b7e3676
               grind)
            | exact superpose b7e3676 b7e25
            | exact resolve b7e25 b7e3676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e3676
          have b7e3984 : False := by grind
          exact b7e3984
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
          have b8e3518 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e74 x y
               grind)
            | exact superpose b8e74 b8e24
            | (have j1 := b8e74 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e74 x y
               grind)
            | exact resolve b8e24 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e3586 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b8e3518
          have b8e3610 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e3586
               have r₂ := b8e23
               grind)
            | exact resolve b8e3586 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3586
          have b8e3658 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3610
               grind)
            | exact superpose b8e3610 b8e20
            | exact resolve b8e20 b8e3610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3610
          have b8e3845 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e3658
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e3658
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e3658 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3658
          have b8e3856 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b8e3845
          have b8e3857 : x = (M.op x x) := by
            first
            | (have r₁ := b8e3856
               have r₂ := b8e22
               grind)
            | exact resolve b8e3856 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3856
          have b8e3858 : False := by grind
          exact b8e3858

/-- `Equation318`: `x ◇ x = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation318 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law318 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law318.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 y x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) x (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e24 (σ x)
           grind)
        | exact superpose b0e24 b0e18
        | exact resolve b0e18 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e53 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e23 x
           grind)
        | exact superpose b0e23 b0e47
        | exact resolve b0e47 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e47
      have b0e54 : False := by grind
      exact b0e54
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 y x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e36 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e23
          | exact resolve b1e23 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e26
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e50 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e35 x
             grind)
          | exact superpose b1e35 b1e50
          | exact resolve b1e50 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e50
        have b1e52 : False := by grind
        exact b1e52
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 y x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e25 y
             grind)
          | exact superpose b2e25 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e25 y
             grind)
          | exact resolve b2e15 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e36 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e38 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e45 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e38 X0 y
             have i₂ := b2e36 (τ X0)
             grind)
          | exact superpose b2e36 b2e38
          | exact resolve b2e38 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e38
        have b2e49 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e45 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e45
          | exact resolve b2e45 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e57 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e66 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e63 X0
             have i₂ := b2e49 X0
             grind)
          | exact superpose b2e49 b2e63
          | (have j0 := b2e63 X0
             grind)
          | exact resolve b2e63 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e63
        have b2e67 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e66 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e70 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e67 (σ x)
             grind)
          | exact superpose b2e67 b2e22
          | (have r₁ := b2e22
             have r₂ := b2e67 (σ x)
             grind)
          | exact resolve b2e22 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e76 : False := by grind
        exact b2e76
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) x (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e39 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e35 (σ X0)
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e51 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : y = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e51
        have b3e54 : y = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e20
             grind)
          | exact resolve b3e53 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e73 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e27 (σ x)
             grind)
          | exact superpose b3e27 b3e23
          | exact resolve b3e23 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e27
        have b3e86 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e39 x
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e39
          | exact resolve b3e39 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e54
        have b3e99 : False := by grind
        exact b3e99
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e46 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e51 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e46
          have b5e54 : y = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e469 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op X2 (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e63 (σ X1) X2 (σ X0)
               grind)
            | exact superpose b5e63 b5e19
            | (have j1 := b5e63 (σ X1) X2 (σ X0)
               grind)
            | exact resolve b5e19 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e943 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X1) X2 (σ X0)
               have i₂ := b5e59 X0 X1
               grind)
            | exact superpose b5e59 b5e13
            | (have j1 := b5e59 X1 X1
               grind)
            | exact resolve b5e13 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e8175 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e469 X0 X1 (σ X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e469
          have b5e10461 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e943 x y X0
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e943
            | (have j0 := b5e943 y y x
               grind)
            | exact resolve b5e943 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e943
          have b5e10652 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e10461 X0
               grind)
            | (have r₁ := b5e10461 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e10461 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10461
          have b5e10688 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e10652 X0
               grind)
            | (have r₁ := b5e10652 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e10652 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10652
          have b5e10765 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e10688 X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e10688 (σ y)
               grind)
            | exact superpose b5e10688 b5e23
            | exact resolve b5e23 b5e10688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10688
          have b5e143571 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e8175 x y
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e8175
            | (have j0 := b5e8175 x y
               grind)
            | exact resolve b5e8175 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e8175
          have b5e143642 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e143571
          have b5e143658 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e143642
               have r₂ := b5e10765 (σ x)
               grind)
            | exact resolve b5e143642 b5e10765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10765 b5e143642
          have b5e143664 : False := by grind
          exact b5e143664
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e25 (σ y)
             grind)
          | exact superpose b6e25 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e25 (σ y)
             grind)
          | exact resolve b6e15 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e41 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e36 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e36
          | exact resolve b6e36 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e44 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e41 X0
             grind)
          | exact superpose b6e41 b6e13
          | exact resolve b6e13 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e45 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e44 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e44
          | exact resolve b6e44 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e60 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e45 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e45
          | (have j1 := b6e17 X0 y
             grind)
          | exact resolve b6e45 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e67 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e60 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e72 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e67 X0
             grind)
          | (have r₁ := b6e67 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e67 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e67 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e76 : x ≠ x := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e72 x
             grind)
          | exact superpose b6e72 b6e21
          | (have r₁ := b6e21
             have r₂ := b6e72 x
             grind)
          | exact resolve b6e21 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e82 : False := by grind
        exact b6e82
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e45 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e53 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e53
            | exact resolve b7e53 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e14
            | exact resolve b7e14 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e58 : y = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e80 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e81 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e21
               grind)
            | exact resolve b7e80 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e83 : y = (M.op x y) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e22
               grind)
            | exact resolve b7e81 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e93 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e83
               grind)
            | exact superpose b7e83 b7e13
            | exact resolve b7e13 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e343 : y = (M.op y y) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e93 x
               grind)
            | exact superpose b7e93 b7e83
            | exact resolve b7e83 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e93
          have b7e354 : False := by grind
          exact b7e354
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e909 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e53 x y
               grind)
            | exact superpose b8e53 b8e20
            | (have j1 := b8e53 y y
               grind)
            | exact resolve b8e20 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e996 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e909
               have r₂ := b8e23
               grind)
            | exact resolve b8e909 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e909
          have b8e1002 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e996
               have r₂ := b8e24
               grind)
            | exact resolve b8e996 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e996
          have b8e1007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1002
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1002
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e1002 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1002
          have b8e1008 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e1007
          have b8e1011 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1008
               have r₂ := b8e21
               grind)
            | exact resolve b8e1008 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1008
          have b8e1014 : False := by grind
          exact b8e1014

/-- `Equation325`: `x ◇ y = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_x_pxy_Equation325 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law325 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e11 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e11 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op X1 X0) X0
           have i₂ := b0e11 X0 X1
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 (M.op X1 X0) X0
           grind)
        | (have r₁ := b0e14 (M.op X0 X0) X0
           have r₂ := b0e11 X0 X0
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e30 X0 X1
           grind)
        | exact superpose b0e30 b0e12
        | exact resolve b0e12 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e22
           grind)
        | exact superpose b0e22 b0e18
        | exact resolve b0e18 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e76 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e70
           have i₂ := b0e21
           grind)
        | exact superpose b0e21 b0e70
        | exact resolve b0e70 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e70
      have b0e139 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e26 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e153 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
        intro X0
        first
        | (have i₁ := b0e51 (M.op (σ X0) (σ X0)) X0
           have i₂ := b0e139 (σ X0)
           grind)
        | exact superpose b0e139 b0e51
        | exact resolve b0e51 b0e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e139
      have b0e156 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e153 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e153
        | exact resolve b0e153 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e233 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e76
           have i₂ := b0e54 x x
           grind)
        | exact superpose b0e54 b0e76
        | (have j1 := b0e54 x x
           grind)
        | exact resolve b0e76 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e254 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e54 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e255 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e54 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e256 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e254 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254
      have b0e263 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e233
      have b0e716 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e256 (τ X0)
           have i₂ := b0e31 X0 (τ X0)
           grind)
        | exact superpose b0e31 b0e256
        | (have j0 := b0e256 (τ X0)
           grind)
        | exact resolve b0e256 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e256
      have b0e718 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e716 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e716
        | (have j0 := b0e716 X0
           grind)
        | exact resolve b0e716 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e716
      have b0e721 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e718 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e718
        | (have j0 := b0e718 X0
           grind)
        | exact resolve b0e718 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e718
      have b0e5342 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e263
           have i₂ := b0e16 x x
           grind)
        | exact superpose b0e16 b0e263
        | (have j1 := b0e16 (σ x) (σ x)
           grind)
        | exact resolve b0e263 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e263
      have b0e5343 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b0e5342
      have b0e5344 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b0e5343
      have b0e5359 : x = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e156 x
           have i₂ := b0e5344
           grind)
        | exact superpose b0e5344 b0e156
        | exact resolve b0e156 b0e5344
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e156 b0e5344
      have b0e5397 : x = (k x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e5359
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e5359
        | exact resolve b0e5359 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5359
      have b0e5400 : x = (M.op x x) := by
        first
        | (have j1 := b0e721 x
           grind)
        | (have r₁ := b0e5397
           have r₂ := b0e721 x
           grind)
        | exact resolve b0e5397 b0e721
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e721 b0e5397
      have b0e5570 : x ≠ x ∨ x = (k x x) := by
        first
        | (have i₁ := b0e26 x x
           have i₂ := b0e5400
           grind)
        | exact superpose b0e5400 b0e26
        | exact resolve b0e26 b0e5400
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e5589 : x = (k x x) := by grind
      clear b0e5570
      have b0e5902 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e255 x x
           have i₂ := b0e5589
           grind)
        | exact superpose b0e5589 b0e255
        | (have j0 := b0e255 x x
           grind)
        | exact resolve b0e255 b0e5589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e255 b0e5589
      have b0e5905 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e5902
      have b0e5906 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e5905
      have b0e5962 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e76
           have i₂ := b0e5906
           grind)
        | exact superpose b0e5906 b0e76
        | exact resolve b0e76 b0e5906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76 b0e5906
      have b0e6013 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e5962
           have i₂ := b0e5400
           grind)
        | exact superpose b0e5400 b0e5962
        | exact resolve b0e5962 b0e5400
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5400 b0e5962
      have b0e6014 : False := by grind
      exact b0e6014
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : x ≠ x ∨ y = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : y = (k x y) := by grind
        clear b1e27
        have b1e40 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e46 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e47 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e46
          | exact resolve b1e46 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e47
          | exact resolve b1e47 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e47
        have b1e49 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e22
          | exact resolve b1e22 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e21
          | exact resolve b1e21 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e57 : False := by grind
        exact b1e57
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : x ≠ x ∨ y = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : y = (k x y) := by grind
        clear b2e27
        have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e160 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e57 x y
             grind)
          | exact superpose b2e57 b2e21
          | (have j1 := b2e57 x y
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
        have b2e176 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e160
        have b2e184 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e176
             have r₂ := b2e22
             grind)
          | exact resolve b2e176 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e176
        have b2e193 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e184
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e184
          | exact resolve b2e184 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e184
        have b2e194 : False := by grind
        exact b2e194
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : y ≠ y ∨ x = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 y x
             grind)
          | (have r₁ := b3e15 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : x = (k y x) := by grind
        clear b3e27
        have b3e38 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b3e38
        have b3e44 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e42
             have r₂ := b3e23
             grind)
          | exact resolve b3e42 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e45 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e46 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e31
             grind)
          | exact superpose b3e31 b3e45
          | exact resolve b3e45 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e45
        have b3e55 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e23
          | exact resolve b3e23 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e56 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e22
          | exact resolve b3e22 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e63 : False := by grind
        exact b3e63
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : y ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y x
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : x = (k y x) := by grind
          clear b5e28
          have b5e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e185 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e1068 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e185 y x
               have i₂ := b5e30
               grind)
            | exact superpose b5e30 b5e185
            | (have j0 := b5e185 y x
               grind)
            | exact resolve b5e185 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e185
          have b5e1072 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e1068
          have b5e1084 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e1072
               have r₂ := b5e24
               grind)
            | exact resolve b5e1072 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1072
          have b5e1090 : False := by grind
          exact b5e1090
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e27 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e28 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e27
          | exact resolve b6e27 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e33 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e28
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e34 : y = (k x y) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e33
          | exact resolve b6e33 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e50 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e34
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e34 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e52 : y = (M.op x y) ∨ x = (M.op y x) := by grind
        clear b6e50
        have b6e55 : x = (M.op y x) := by
          first
          | (have r₁ := b6e52
             have r₂ := b6e21
             grind)
          | exact resolve b6e52 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e58 : False := by grind
        exact b6e58
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ x)
               grind)
            | (have r₁ := b7e16 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e28
          have b7e31 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e30
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e30
            | exact resolve b7e30 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e36 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e31
               grind)
            | exact superpose b7e31 b7e14
            | exact resolve b7e14 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e37 : x = (k y x) := by
            first
            | (have i₁ := b7e36
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e36
            | exact resolve b7e36 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e48 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e37
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e37
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e37 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e50 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b7e48
          have b7e53 : y = (M.op x y) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e21
               grind)
            | exact resolve b7e50 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e56 : False := by grind
          exact b7e56
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e142 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e43 x y
               grind)
            | exact superpose b8e43 b8e23
            | (have j1 := b8e43 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e43 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e43 y x
               grind)
            | exact resolve b8e23 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e158 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e142
          have b8e166 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e158
               have r₂ := b8e24
               grind)
            | exact resolve b8e158 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158
          have b8e175 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e166
               grind)
            | exact superpose b8e166 b8e20
            | exact resolve b8e20 b8e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166
          have b8e238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e175
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e175
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e175 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175
          have b8e239 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b8e238
          have b8e240 : x = (M.op y x) := by
            first
            | (have r₁ := b8e239
               have r₂ := b8e22
               grind)
            | exact resolve b8e239 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e239
          have b8e241 : False := by grind
          exact b8e241

/-- `Equation325`: `x ◇ y = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_x_pyx_Equation325 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law325 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e11 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e11 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op X1 X0) X0
           have i₂ := b0e11 X0 X1
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 (M.op X1 X0) X0
           grind)
        | (have r₁ := b0e14 (M.op X0 X0) X0
           have r₂ := b0e11 X0 X0
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e30 X0 X1
           grind)
        | exact superpose b0e30 b0e12
        | exact resolve b0e12 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e16 (σ X1) (σ X0)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e22
           grind)
        | exact superpose b0e22 b0e18
        | exact resolve b0e18 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e76 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e70
           have i₂ := b0e21
           grind)
        | exact superpose b0e21 b0e70
        | exact resolve b0e70 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e70
      have b0e139 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e26 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e153 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
        intro X0
        first
        | (have i₁ := b0e51 (M.op (σ X0) (σ X0)) X0
           have i₂ := b0e139 (σ X0)
           grind)
        | exact superpose b0e139 b0e51
        | exact resolve b0e51 b0e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e139
      have b0e154 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e153 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e153
        | exact resolve b0e153 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e231 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e76
           have i₂ := b0e54 x x
           grind)
        | exact superpose b0e54 b0e76
        | (have j1 := b0e54 x x
           grind)
        | exact resolve b0e76 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e252 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e54 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e253 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e54 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e254 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e252 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e252
      have b0e261 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e231
      have b0e706 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e254 (τ X0)
           have i₂ := b0e31 X0 (τ X0)
           grind)
        | exact superpose b0e31 b0e254
        | (have j0 := b0e254 (τ X0)
           grind)
        | exact resolve b0e254 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e254
      have b0e708 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e706 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e706
        | (have j0 := b0e706 X0
           grind)
        | exact resolve b0e706 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e706
      have b0e711 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e708 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e708
        | (have j0 := b0e708 X0
           grind)
        | exact resolve b0e708 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e708
      have b0e5259 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e261
           have i₂ := b0e16 x x
           grind)
        | exact superpose b0e16 b0e261
        | (have j1 := b0e16 (σ x) (σ x)
           grind)
        | exact resolve b0e261 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e261
      have b0e5260 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b0e5259
      have b0e5261 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b0e5260
      have b0e5276 : x = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e154 x
           have i₂ := b0e5261
           grind)
        | exact superpose b0e5261 b0e154
        | exact resolve b0e154 b0e5261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e154 b0e5261
      have b0e5314 : x = (k x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e5276
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e5276
        | exact resolve b0e5276 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5276
      have b0e5317 : x = (M.op x x) := by
        first
        | (have j1 := b0e711 x
           grind)
        | (have r₁ := b0e5314
           have r₂ := b0e711 x
           grind)
        | exact resolve b0e5314 b0e711
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e711 b0e5314
      have b0e5484 : x ≠ x ∨ x = (k x x) := by
        first
        | (have i₁ := b0e26 x x
           have i₂ := b0e5317
           grind)
        | exact superpose b0e5317 b0e26
        | exact resolve b0e26 b0e5317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e5503 : x = (k x x) := by grind
      clear b0e5484
      have b0e5816 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e253 x x
           have i₂ := b0e5503
           grind)
        | exact superpose b0e5503 b0e253
        | (have j0 := b0e253 x x
           grind)
        | exact resolve b0e253 b0e5503
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e253 b0e5503
      have b0e5819 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e5816
      have b0e5820 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e5819
      have b0e5876 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e76
           have i₂ := b0e5820
           grind)
        | exact superpose b0e5820 b0e76
        | exact resolve b0e76 b0e5820
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76 b0e5820
      have b0e5927 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e5876
           have i₂ := b0e5317
           grind)
        | exact superpose b0e5317 b0e5876
        | exact resolve b0e5876 b0e5317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5317 b0e5876
      have b0e5928 : False := by grind
      exact b0e5928
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : x ≠ x ∨ y = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : y = (k x y) := by grind
        clear b1e27
        have b1e40 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e46 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e47 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e46
          | exact resolve b1e46 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e47
          | exact resolve b1e47 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e47
        have b1e49 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e22
          | exact resolve b1e22 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e21
          | exact resolve b1e21 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e57 : False := by grind
        exact b1e57
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b2e12 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e25 : (M.op y x) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b2e12 y x
             have i₂ := b2e23
             grind)
          | exact superpose b2e23 b2e12
          | exact resolve b2e12 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26 : x = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b2e25
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e25
          | exact resolve b2e25 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e27 : x ≠ x ∨ y = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (M.op X1 X0) X0
             have i₂ := b2e12 X0 X1
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op X1 X0) X0
             grind)
          | (have r₁ := b2e15 (M.op X0 X0) X0
             have r₂ := b2e12 X0 X0
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : y = (k x y) := by grind
        clear b2e27
        have b2e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e31 X0 X1
             grind)
          | exact superpose b2e31 b2e13
          | exact resolve b2e13 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 (M.op X1 X0)
             have i₂ := b2e12 X0 X1
             grind)
          | exact superpose b2e12 b2e16
          | (have j0 := b2e16 X0 (M.op X1 X0)
             grind)
          | (have r₁ := b2e16 X0 (M.op X0 X0)
             have r₂ := b2e12 X0 X0
             grind)
          | exact resolve b2e16 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : y = (M.op x y) ∨ y = (k y x) := by grind
        clear b2e39
        have b2e45 : y = (k y x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b2e43
             have i₂ := b2e23
             grind)
          | exact superpose b2e23 b2e43
          | exact resolve b2e43 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e43
        have b2e57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e94 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e28 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e110 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e41 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e127 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b2e38 (M.op (σ X0) (σ X0)) X0
             have i₂ := b2e94 (σ X0)
             grind)
          | exact superpose b2e94 b2e38
          | exact resolve b2e38 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e133 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e127 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e127
          | exact resolve b2e127 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127
        have b2e148 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (σ X0) (σ X1)
             have i₂ := b2e57 X1 X0
             grind)
          | exact superpose b2e57 b2e12
          | (have j1 := b2e57 X1 X0
             grind)
          | exact resolve b2e12 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e158 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e57 x y
             grind)
          | exact superpose b2e57 b2e21
          | (have j1 := b2e57 x y
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
        have b2e159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (σ X0) (σ X1)
             have i₂ := b2e57 X0 X1
             grind)
          | exact superpose b2e57 b2e12
          | (have j1 := b2e57 X0 X1
             grind)
          | exact resolve b2e12 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e161 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X1) (σ X0)
             have i₂ := b2e57 X0 X1
             grind)
          | exact superpose b2e57 b2e16
          | (have j0 := b2e16 (σ X1) (σ X0)
             have j1 := b2e57 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e57 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e57 X0 X1
             grind)
          | exact resolve b2e16 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e171 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e161 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e161
        have b2e172 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e171 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171
        have b2e174 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e158
        have b2e180 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e172 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e172
          | (have j0 := b2e172 X0 X1
             grind)
          | exact resolve b2e172 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172
        have b2e182 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e174
             have r₂ := b2e22
             grind)
          | exact resolve b2e174 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174
        have b2e205 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e182
             grind)
          | exact superpose b2e182 b2e22
          | exact resolve b2e22 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e206 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (k y x))) := by
          first
          | (have i₁ := b2e12 (σ y) (σ x)
             have i₂ := b2e182
             grind)
          | exact superpose b2e182 b2e12
          | exact resolve b2e12 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e214 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b2e205
             have i₂ := b2e45
             grind)
          | exact superpose b2e45 b2e205
          | exact resolve b2e205 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e216 : y = (M.op x x) := by grind
        clear b2e214
        have b2e218 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e110 (σ x)
             have i₂ := b2e57 x x
             grind)
          | exact superpose b2e57 b2e110
          | (have j1 := b2e57 X0 X0
             grind)
          | exact resolve b2e110 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110
        have b2e225 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e218 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e218
        have b2e228 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e225 X0
             have i₂ := b2e18 X0 (k X0 X0)
             grind)
          | exact superpose b2e18 b2e225
          | (have j0 := b2e225 X0
             grind)
          | exact resolve b2e225 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e225
        have b2e231 : x = (M.op y y) := by
          first
          | (have i₁ := b2e26
             have i₂ := b2e216
             grind)
          | exact superpose b2e216 b2e26
          | exact resolve b2e26 b2e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e242 : x = (k y x) := by
          first
          | (have i₁ := b2e94 x
             have i₂ := b2e216
             grind)
          | exact superpose b2e216 b2e94
          | exact resolve b2e94 b2e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94 b2e216
        have b2e268 : x ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b2e15 y y
             have i₂ := b2e231
             grind)
          | exact superpose b2e231 b2e15
          | (have j0 := b2e15 y y
             grind)
          | exact resolve b2e15 b2e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e343 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e205
             have i₂ := b2e242
             grind)
          | exact superpose b2e242 b2e205
          | exact resolve b2e205 b2e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e205
        have b2e1227 : (M.op (σ y) (σ x)) = (σ (k (k y x) y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (k (k y x) y)) := by
          first
          | (have i₁ := b2e180 y (k y x)
             have i₂ := b2e206
             grind)
          | exact superpose b2e206 b2e180
          | (have j0 := b2e180 y (k y x)
             grind)
          | exact resolve b2e180 b2e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e206
        have b2e1255 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (k (k y x) y)) := by
          first
          | (have i₁ := b2e1227
             have i₂ := b2e242
             grind)
          | exact superpose b2e242 b2e1227
          | exact resolve b2e1227 b2e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1227
        have b2e1264 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (k (k y x) y)) := by
          first
          | (have i₁ := b2e1255
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e1255
          | exact resolve b2e1255 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1255
        have b2e1271 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k (k y x) y)) := by
          first
          | (have i₁ := b2e1264
             have i₂ := b2e242
             grind)
          | exact superpose b2e242 b2e1264
          | exact resolve b2e1264 b2e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1264
        have b2e1278 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (k (k y x) y)) := by
          first
          | (have r₁ := b2e1271
             have r₂ := b2e21
             grind)
          | exact resolve b2e1271 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1271
        have b2e1283 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e1278
             have i₂ := b2e242
             grind)
          | exact superpose b2e242 b2e1278
          | exact resolve b2e1278 b2e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1278
        have b2e1288 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e1283
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e1283
          | exact resolve b2e1283 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e1283
        have b2e1292 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e1288
             have r₂ := b2e343
             grind)
          | exact resolve b2e1288 b2e343
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1288
        have b2e1536 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e159 X0 X1
             have i₂ := b2e57 X0 X0
             grind)
          | exact superpose b2e57 b2e159
          | (have j0 := b2e159 X0 X1
             have j1 := b2e57 X0 X1
             grind)
          | exact resolve b2e159 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e159
        have b2e1637 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e1536 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1536
        have b2e22595 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e228 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e228
          | exact resolve b2e228 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228
        have b2e22676 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22595 X0
             have i₂ := b2e32 X0 (τ X0)
             grind)
          | exact superpose b2e32 b2e22595
          | (have j0 := b2e22595 X0
             grind)
          | exact resolve b2e22595 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22595
        have b2e22707 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22676 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e22676
          | (have j0 := b2e22676 X0
             grind)
          | exact resolve b2e22676 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22676
        have b2e22731 : ∀ X0 : G, (k X0 (σ (k (τ X0) (τ X0)))) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22707 X0
             have i₂ := b2e31 X0 (k (τ X0) (τ X0))
             grind)
          | exact superpose b2e31 b2e22707
          | (have j0 := b2e22707 X0
             grind)
          | exact resolve b2e22707 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22707
        have b2e22755 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22731 X0
             have i₂ := b2e32 X0 (τ X0)
             grind)
          | exact superpose b2e32 b2e22731
          | (have j0 := b2e22731 X0
             grind)
          | exact resolve b2e22731 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22731
        have b2e22775 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22755 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e22755
          | (have j0 := b2e22755 X0
             grind)
          | exact resolve b2e22755 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22755
        have b2e83371 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e1637 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1637
        have b2e83373 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e83371 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83371
        have b2e83436 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e83373 X0
             have j1 := b2e180 X0 X0
             grind)
          | (have r₁ := b2e83373 X0
             have r₂ := b2e180 X0 X0
             grind)
          | exact resolve b2e83373 b2e180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180 b2e83373
        have b2e83511 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e83436 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e83436
          | exact resolve b2e83436 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83436
        have b2e83577 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e83511 X0
             have i₂ := b2e32 X0 (τ X0)
             grind)
          | exact superpose b2e32 b2e83511
          | (have j0 := b2e83511 X0
             grind)
          | exact resolve b2e83511 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e83511
        have b2e83584 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e83577 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e83577
          | (have j0 := b2e83577 X0
             grind)
          | exact resolve b2e83577 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83577
        have b2e84066 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e31 X0 (τ X0)
             have i₂ := b2e83584 (τ X0)
             grind)
          | exact superpose b2e83584 b2e31
          | (have j1 := b2e83584 (τ X0)
             grind)
          | exact resolve b2e31 b2e83584
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e83584
        have b2e84145 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e84066 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e84066
          | (have j0 := b2e84066 X0
             grind)
          | exact resolve b2e84066 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84066
        have b2e84649 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e84145 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e84145
          | exact resolve b2e84145 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84145
        have b2e84692 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e84649 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e84649
          | (have j0 := b2e84649 X0
             grind)
          | exact resolve b2e84649 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84649
        have b2e85030 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e38 X1 (k X0 X0)
             have i₂ := b2e84692 X0
             grind)
          | exact superpose b2e84692 b2e38
          | (have j1 := b2e84692 X0
             grind)
          | exact resolve b2e38 b2e84692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84692
        have b2e85065 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e85030 X0 X1
             have i₂ := b2e38 X1 (M.op X0 X0)
             grind)
          | exact superpose b2e38 b2e85030
          | (have j0 := b2e85030 X0 X1
             grind)
          | exact resolve b2e85030 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e85030
        have b2e87010 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e85065 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e85065
          | (have j0 := b2e85065 X1 X1
             grind)
          | exact resolve b2e85065 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85065
        have b2e87240 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22775 X0
             have i₂ := b2e87010 X0 X0
             grind)
          | exact superpose b2e87010 b2e22775
          | (have j0 := b2e22775 X0
             have j1 := b2e87010 X0 X0
             grind)
          | exact resolve b2e22775 b2e87010
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22775
        have b2e87336 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e87240 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87240
        have b2e91785 : y = (k y x) ∨ y = (M.op (k y y) y) ∨ x = y := by
          first
          | (have i₁ := b2e87336 y
             have i₂ := b2e231
             grind)
          | exact superpose b2e231 b2e87336
          | (have j0 := b2e87336 y
             grind)
          | exact resolve b2e87336 b2e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87336
        have b2e91794 : x = y ∨ y = (M.op (k y y) y) ∨ x = y := by
          first
          | (have i₁ := b2e91785
             have i₂ := b2e242
             grind)
          | exact superpose b2e242 b2e91785
          | exact resolve b2e91785 b2e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91785
        have b2e91795 : y = (M.op (k y y) y) ∨ x = y := by grind
        clear b2e91794
        have b2e92019 : y ≠ y ∨ (k y y) = (k y (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e15 y (k y y)
             have i₂ := b2e91795
             grind)
          | exact superpose b2e91795 b2e15
          | (have j0 := b2e15 y (k y y)
             grind)
          | (have r₁ := b2e15 y (k y y)
             have r₂ := b2e91795
             grind)
          | exact resolve b2e15 b2e91795
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91795
        have b2e92046 : (k y y) = (k y (k y y)) ∨ x = y := by grind
        clear b2e92019
        have b2e93670 : (k y y) = (k y (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e87010 y y
             have i₂ := b2e92046
             grind)
          | exact superpose b2e92046 b2e87010
          | (have j0 := b2e87010 x y
             grind)
          | exact resolve b2e87010 b2e92046
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87010 b2e92046
        have b2e93683 : (k y x) = (k y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e93670
             have i₂ := b2e231
             grind)
          | exact superpose b2e231 b2e93670
          | exact resolve b2e93670 b2e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93670
        have b2e93693 : x = (k y y) ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e93683
             have i₂ := b2e242
             grind)
          | exact superpose b2e242 b2e93683
          | exact resolve b2e93683 b2e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e242 b2e93683
        have b2e93701 : x = y ∨ x = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e93693
             have i₂ := b2e231
             grind)
          | exact superpose b2e231 b2e93693
          | exact resolve b2e93693 b2e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e231 b2e93693
        have b2e93702 : x = (k y y) ∨ x = y := by grind
        clear b2e93701
        have b2e94623 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e148 y y
             have i₂ := b2e93702
             grind)
          | exact superpose b2e93702 b2e148
          | (have j0 := b2e148 y y
             grind)
          | exact resolve b2e148 b2e93702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e148
        have b2e94656 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b2e94623
        have b2e94692 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e94656
             have i₂ := b2e1292
             grind)
          | exact superpose b2e1292 b2e94656
          | exact resolve b2e94656 b2e1292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1292 b2e94656
        have b2e94693 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b2e94692
        have b2e96396 : y = (k (τ (σ y)) y) ∨ x = y := by
          first
          | (have i₁ := b2e133 y
             have i₂ := b2e94693
             grind)
          | exact superpose b2e94693 b2e133
          | exact resolve b2e133 b2e94693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e133 b2e94693
        have b2e96477 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e96396
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e96396
          | exact resolve b2e96396 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96396
        have b2e96480 : y = (k y y) := by
          first
          | (have r₁ := b2e96477
             have r₂ := b2e268
             grind)
          | exact resolve b2e96477 b2e268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e268 b2e96477
        have b2e96782 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e93702
             have i₂ := b2e96480
             grind)
          | exact superpose b2e96480 b2e93702
          | exact resolve b2e93702 b2e96480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93702 b2e96480
        have b2e96874 : x = y := by grind
        clear b2e96782
        have b2e97254 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e343
             have i₂ := b2e96874
             grind)
          | exact superpose b2e96874 b2e343
          | exact resolve b2e343 b2e96874
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e343 b2e96874
        have b2e97258 : False := by grind
        exact b2e97258
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : y ≠ y ∨ x = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 y x
             grind)
          | (have r₁ := b3e15 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : x = (k y x) := by grind
        clear b3e27
        have b3e38 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b3e38
        have b3e44 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e42
             have r₂ := b3e23
             grind)
          | exact resolve b3e42 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e45 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e46 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e45
             have i₂ := b3e31
             grind)
          | exact superpose b3e31 b3e45
          | exact resolve b3e45 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e45
        have b3e55 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e23
          | exact resolve b3e23 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e56 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e22
          | exact resolve b3e22 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e63 : False := by grind
        exact b3e63
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e35 : y ≠ y ∨ x = (M.op y x) ∨ x = (k x y) := by
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
          have b5e38 : x = (M.op y x) ∨ x = (k x y) := by grind
          clear b5e35
          have b5e39 : x = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e21
               grind)
            | exact resolve b5e38 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e181 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e1051 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e181 y x
               have i₂ := b5e39
               grind)
            | exact superpose b5e39 b5e181
            | (have j0 := b5e181 y x
               grind)
            | exact resolve b5e181 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e181
          have b5e1057 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e1051
          have b5e1062 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e1057
               have r₂ := b5e24
               grind)
            | exact resolve b5e1057 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1057
          have b5e1068 : False := by grind
          exact b5e1068
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e12 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X1 X0) X0
             have i₂ := b6e12 X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (M.op X1 X0) X0
             have i₂ := b6e12 X0 X1
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X1 X0) X0
             grind)
          | (have r₁ := b6e15 (M.op X0 X0) X0
             have r₂ := b6e12 X0 X0
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e28 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e27
          | exact resolve b6e27 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 (τ X0) X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e28
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e34 : y = (k x y) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e33
          | exact resolve b6e33 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e37 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 (M.op X1 X0)
             have i₂ := b6e12 X0 X1
             grind)
          | exact superpose b6e12 b6e16
          | (have j0 := b6e16 X0 (M.op X1 X0)
             grind)
          | (have r₁ := b6e16 X0 (M.op X0 X0)
             have r₂ := b6e12 X0 X0
             grind)
          | exact resolve b6e16 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b6e37
        have b6e40 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e23
             grind)
          | exact superpose b6e23 b6e39
          | exact resolve b6e39 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e41 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e40
          | exact resolve b6e40 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e45 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e29 X0 X1
             grind)
          | exact superpose b6e29 b6e13
          | exact resolve b6e13 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e50 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e34
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e34 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e53 : y = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e50
             have r₂ := b6e21
             grind)
          | exact resolve b6e50 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e56 : y = (M.op y x) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e20
             grind)
          | exact resolve b6e53 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e58 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e20
          | exact resolve b6e20 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e125 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e26 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e136 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b6e45 (M.op (σ X0) (σ X0)) X0
             have i₂ := b6e125 (σ X0)
             grind)
          | exact superpose b6e125 b6e45
          | exact resolve b6e45 b6e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45 b6e125
        have b6e137 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e136 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e136
          | exact resolve b6e136 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e136
        have b6e143 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e24 (σ x) (σ x)
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e24
          | exact resolve b6e24 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e152 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e143
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e143
          | exact resolve b6e143 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e143
        have b6e181 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e38 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e304 : x = (k (τ (σ y)) x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e137 x
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e137
          | exact resolve b6e137 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e137
        have b6e319 : (σ y) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e304
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e304
          | exact resolve b6e304 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e304
        have b6e396 : (τ (σ y)) = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e319
             grind)
          | exact superpose b6e319 b6e13
          | exact resolve b6e13 b6e319
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e319
        have b6e414 : y = (k y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e396
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e396
          | exact resolve b6e396 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e396
        have b6e457 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e414
             grind)
          | exact superpose b6e414 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e414
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e414
        have b6e459 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
        clear b6e457
        have b6e461 : x = (M.op y x) ∨ x = (k y x) := by
          first
          | (have r₁ := b6e459
             have r₂ := b6e21
             grind)
          | exact resolve b6e459 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e459
        have b6e463 : x = (k y x) := by
          first
          | (have r₁ := b6e461
             have r₂ := b6e20
             grind)
          | exact resolve b6e461 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e461
        have b6e667 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e181 (σ y)
             have i₂ := b6e152
             grind)
          | exact superpose b6e152 b6e181
          | exact resolve b6e181 b6e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e152 b6e181
        have b6e677 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e667
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e667
          | exact resolve b6e667 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e667
        have b6e678 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b6e677
        have b6e693 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e678
             have i₂ := b6e463
             grind)
          | exact superpose b6e463 b6e678
          | exact resolve b6e678 b6e463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e463 b6e678
        have b6e695 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e693
             have i₂ := b6e23
             grind)
          | exact superpose b6e23 b6e693
          | exact resolve b6e693 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e693
        have b6e877 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e48 x x
             have i₂ := b6e695
             grind)
          | exact superpose b6e695 b6e48
          | exact resolve b6e48 b6e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e695
        have b6e900 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e877
        have b6e1071 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e900
             grind)
          | exact superpose b6e900 b6e13
          | exact resolve b6e13 b6e900
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1102 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1071
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1071
          | exact resolve b6e1071 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1071
        have b6e1112 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e1102
             grind)
          | exact superpose b6e1102 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e1102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1102
        have b6e1113 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1112
        have b6e3655 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e12 x x
             have i₂ := b6e1113
             grind)
          | exact superpose b6e1113 b6e12
          | exact resolve b6e12 b6e1113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1113
        have b6e3700 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3655
             have r₂ := b6e21
             grind)
          | exact resolve b6e3655 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3655
        have b6e3794 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e26 x x
             have i₂ := b6e3700
             grind)
          | exact superpose b6e3700 b6e26
          | exact resolve b6e26 b6e3700
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26 b6e3700
        have b6e3813 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3794
        have b6e3948 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e900
             have i₂ := b6e3813
             grind)
          | exact superpose b6e3813 b6e900
          | exact resolve b6e900 b6e3813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e900 b6e3813
        have b6e3970 : (σ x) = (σ y) := by grind
        clear b6e3948
        have b6e4162 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3970
             grind)
          | exact superpose b6e3970 b6e13
          | exact resolve b6e13 b6e3970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3970
        have b6e4223 : x = y := by
          first
          | (have i₁ := b6e4162
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4162
          | exact resolve b6e4162 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4162
        have b6e4226 : False := by grind
        exact b6e4226
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e43 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e44 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e64 : (τ (σ x)) = (k x y) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e14
            | exact resolve b7e14 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e65 : x = (k x y) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e64
            | exact resolve b7e64 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e76 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e77 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b7e76
          have b7e79 : y = (M.op x y) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e21
               grind)
            | exact resolve b7e77 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e81 : False := by grind
          exact b7e81
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e140 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e43 x y
               grind)
            | exact superpose b8e43 b8e23
            | (have j1 := b8e43 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e43 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e43 y x
               grind)
            | exact resolve b8e23 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e156 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e140
          have b8e164 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e156
               have r₂ := b8e24
               grind)
            | exact resolve b8e156 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e173 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e164
               grind)
            | exact superpose b8e164 b8e20
            | exact resolve b8e20 b8e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164
          have b8e236 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e173
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e173
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e173 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e237 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e236
          have b8e238 : y = (M.op x y) := by
            first
            | (have r₁ := b8e237
               have r₂ := b8e21
               grind)
            | exact resolve b8e237 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e237
          have b8e239 : False := by grind
          exact b8e239
