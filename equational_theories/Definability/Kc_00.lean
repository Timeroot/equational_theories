import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation106`: `x = x ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation106 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law106 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law106.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 x x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
           have i₂ := b0e11 (M.op X0 X1) x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : x = (M.op x y) := by
        first
        | (have i₁ := b0e25 (M.op (M.op x y) x)
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e25
        | exact resolve b0e25 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25
      have b0e46 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e28 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e28
        | exact resolve b0e28 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e203 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e18
        | exact resolve b0e18 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e212 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e203
           have i₂ := b0e31
           grind)
        | exact superpose b0e31 b0e203
        | exact resolve b0e203 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e203
      have b0e213 : False := by grind
      exact b0e213
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
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
        have b1e36 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e39 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e36
        have b1e41 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e39
             have r₂ := b1e21
             grind)
          | exact resolve b1e39 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e43 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e41
          | exact resolve b1e41 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e44 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e43
          | exact resolve b1e43 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e43
        have b1e48 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e13
          | exact resolve b1e13 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e49 : x = y := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e48
          | exact resolve b1e48 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e67 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e24
          | exact resolve b1e24 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e49
        have b1e69 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e67
          | exact resolve b1e67 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e70 : False := by grind
        exact b1e70
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
          intro X0 X1 X2
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
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e25 : ∀ X0 : G, x = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 x x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : x = (M.op x y) := by
          first
          | (have i₁ := b2e25 (M.op (M.op x y) x)
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e25
          | exact resolve b2e25 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e348 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e60 x y
             grind)
          | exact superpose b2e60 b2e19
          | (have j1 := b2e60 x y
             grind)
          | exact resolve b2e19 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e391 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e348
             have r₂ := b2e21
             grind)
          | exact resolve b2e348 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e348
        have b2e396 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e391
             have r₂ := b2e22
             grind)
          | exact resolve b2e391 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e391
        have b2e397 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e396
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e396
          | exact resolve b2e396 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e396
        have b2e398 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e397
             have i₂ := b2e28
             grind)
          | exact superpose b2e28 b2e397
          | exact resolve b2e397 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e397
        have b2e399 : False := by grind
        exact b2e399
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
        have b3e45 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e50 : y = (M.op x x) ∨ y = (k x y) := by grind
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
        have b3e53 : x = y := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e52
          | exact resolve b3e52 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e52
        have b3e55 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e24
          | exact resolve b3e24 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e60 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e55
          | exact resolve b3e55 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e61 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e60
          | exact resolve b3e60 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e60
        have b3e62 : False := by grind
        exact b3e62
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
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
          have b5e27 : ∀ X0 : G, y = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 y x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X2) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X1 X0) X2) X0 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
               have i₂ := b5e13 (M.op X0 X1) x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : y = (M.op y x) := by
            first
            | (have i₁ := b5e27 (M.op (M.op x x) x)
               have i₂ := b5e13 x x x
               grind)
            | exact superpose b5e13 b5e27
            | exact resolve b5e27 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e36 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X2) = (M.op X0 X0) ∨ (M.op (M.op X1 X0) X2) = (k X0 (M.op (M.op X1 X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X0 (M.op (M.op X1 X0) X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X0 (M.op (M.op X1 X0) X2)
               grind)
            | (have r₁ := b5e17 X0 (M.op (M.op X1 X0) X2)
               have r₂ := b5e13 X0 X1 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (k X0 (M.op (M.op X1 X0) X2)) ∨ (M.op (M.op X1 X0) X2) = (M.op X0 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e37 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e43 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e36
          have b5e44 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X0) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 X0 (M.op (M.op X1 X0) X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e29
            | exact resolve b5e29 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X0 (M.op X1 X0)
               have i₂ := b5e29 X1 X0
               grind)
            | exact superpose b5e29 b5e29
            | exact resolve b5e29 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X1 X1
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e29 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e29
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e29 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 X0) X0 X2
               have i₂ := b5e29 X1 X0
               grind)
            | exact superpose b5e29 b5e13
            | exact resolve b5e13 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e68 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b5e72 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e33 X0 X1
               grind)
            | exact superpose b5e33 b5e14
            | exact resolve b5e14 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e73 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e68 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e68
            | exact resolve b5e68 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e34 X1 X0
               grind)
            | exact superpose b5e34 b5e14
            | exact resolve b5e14 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e102 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (M.op X0 X1) X1
               have i₂ := b5e57 X1 X0
               grind)
            | exact superpose b5e57 b5e17
            | (have j0 := b5e17 (M.op X0 X1) X1
               grind)
            | (have r₁ := b5e17 (M.op X1 X0) X0
               have r₂ := b5e57 X0 X1
               grind)
            | exact resolve b5e17 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e104 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e131 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X1 X3) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X1 X3) = (k (M.op (M.op X0 X1) X2) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e17 (M.op (M.op X0 X1) X2) (M.op X1 X3)
               have i₂ := b5e28 X1 X0 X2 X3
               grind)
            | exact superpose b5e28 b5e17
            | (have j0 := b5e17 (M.op (M.op X0 X1) X2) (M.op X1 X3)
               grind)
            | (have r₁ := b5e17 (M.op (M.op X1 X0) X2) (M.op X0 X3)
               have r₂ := b5e28 X0 X1 X2 X3
               grind)
            | exact resolve b5e17 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e133 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) ∨ (M.op X1 X3) = (k (M.op (M.op X0 X1) X2) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e131 X0 X1 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e257 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X1 X0) (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42 (M.op X0 X1) X1 X2
               have i₂ := b5e29 X0 X1
               grind)
            | exact superpose b5e29 b5e42
            | exact resolve b5e42 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e285 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e72 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e72
            | exact resolve b5e72 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e368 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) X3) = (M.op (M.op (M.op X2 (σ X0)) X3) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e28 (σ X0) X2 X3 (σ X1)
               have i₂ := b5e48 X0 X1
               grind)
            | exact superpose b5e48 b5e28
            | (have j1 := b5e48 X0 X1
               grind)
            | exact resolve b5e28 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e369 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 (σ X0) (σ X1)
               have i₂ := b5e48 X0 X1
               grind)
            | exact superpose b5e48 b5e29
            | (have j1 := b5e48 X0 X1
               grind)
            | exact resolve b5e29 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e389 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 (σ X1) (σ X1)
               have i₂ := b5e48 X1 X0
               grind)
            | exact superpose b5e48 b5e29
            | (have j1 := b5e48 X1 X0
               grind)
            | exact resolve b5e29 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e389 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e389
          have b5e415 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e89
          have b5e430 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e415 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e415
            | exact resolve b5e415 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e415
          have b5e578 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 (M.op X0 X1) (M.op X1 X2)
               have i₂ := b5e62 X1 X0 X2
               grind)
            | exact superpose b5e62 b5e29
            | exact resolve b5e29 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e634 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e73 X0
               have i₂ := b5e66 (σ (M.op (τ X0) (τ X0))) X0
               grind)
            | exact superpose b5e66 b5e73
            | (have j1 := b5e66 (σ (M.op (τ X0) (τ X0))) X0
               grind)
            | exact resolve b5e73 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e636 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e430 X0
               have i₂ := b5e66 (τ (M.op (σ X0) (σ X0))) X0
               grind)
            | exact superpose b5e66 b5e430
            | (have j1 := b5e66 (τ (M.op (σ X0) (σ X0))) X0
               grind)
            | exact resolve b5e430 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e430
          have b5e643 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have j0 := b5e636 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e636
          have b5e644 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have j0 := b5e634 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e634
          have b5e649 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e644 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e644
            | exact resolve b5e644 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e644
          have b5e730 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e643 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e643
            | exact resolve b5e643 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e828 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e29 (σ X0) (σ (M.op X0 X0))
               have i₂ := b5e649 X0
               grind)
            | exact superpose b5e649 b5e29
            | exact resolve b5e29 b5e649
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e649
          have b5e938 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e29 (τ X0) (τ (M.op X0 X0))
               have i₂ := b5e730 X0
               grind)
            | exact superpose b5e730 b5e29
            | exact resolve b5e29 b5e730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e730
          have b5e1270 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op X0 X1) X3) (M.op X2 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e56 (M.op X0 X1) (M.op X1 X2) X2
               have i₂ := b5e578 X0 X1 X2
               grind)
            | exact superpose b5e578 b5e56
            | exact resolve b5e56 b5e578
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e578
          have b5e2052 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 (σ X0) (σ X1)
               have i₂ := b5e397 X1 X0
               grind)
            | exact superpose b5e397 b5e29
            | (have j1 := b5e397 (k X0 X1) X1
               grind)
            | exact resolve b5e29 b5e397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2863 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) = X2 ∨ (M.op X1 X2) = (k (M.op X0 X1) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 X1 X2
               have i₂ := b5e257 X1 X0 X2
               grind)
            | exact superpose b5e257 b5e29
            | (have j1 := b5e257 X1 X0 X2
               grind)
            | exact resolve b5e29 b5e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e257
          have b5e4117 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e369 x y
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e369
            | (have j0 := b5e369 y y
               grind)
            | exact resolve b5e369 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e369
          have b5e4289 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e4117
               have r₂ := b5e23
               grind)
            | exact resolve b5e4117 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4117
          have b5e4294 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b5e4289
               have r₂ := b5e24
               grind)
            | exact resolve b5e4289 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4289
          have b5e4317 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
            first
            | (have i₁ := b5e938 (σ y)
               have i₂ := b5e4294
               grind)
            | exact superpose b5e4294 b5e938
            | exact resolve b5e938 b5e4294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e938 b5e4294
          have b5e4351 : y = (M.op y y) := by
            first
            | (have i₁ := b5e4317
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e4317
            | exact resolve b5e4317 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4317
          have b5e4770 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (k (M.op (M.op X2 X0) X3) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op (M.op X2 X0) X3) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e6750 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (M.op X0 (σ x)) X1) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e368 x y X0 X1
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e368
            | (have j0 := b5e368 x y x x
               grind)
            | exact resolve b5e368 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e368
          have b5e6833 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (M.op X0 (σ x)) X1) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e6750 X0 X1
               grind)
            | (have r₁ := b5e6750 X0 X1
               have r₂ := b5e23
               grind)
            | exact resolve b5e6750 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6750
          have b5e6843 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op (M.op X0 (σ x)) X1) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e6833 X0 X1
               grind)
            | (have r₁ := b5e6833 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e6833 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6833
          have b5e11060 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op X0 (σ x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e6843 X0 (M.op X0 (σ x))
               have i₂ := b5e104 X0 (σ x)
               grind)
            | exact superpose b5e104 b5e6843
            | (have j1 := b5e104 X0 (σ x)
               grind)
            | exact resolve b5e6843 b5e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e11129 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ x)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 (M.op (M.op X0 (σ x)) X1) (σ y)
               have i₂ := b5e6843 X0 X1
               grind)
            | exact superpose b5e6843 b5e29
            | exact resolve b5e29 b5e6843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6843
          have b5e11168 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ x)) (σ x)) := by
            intro X0
            first
            | (have j0 := b5e11060 X0
               grind)
            | (have r₁ := b5e11060 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e11060 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11060
          have b5e11188 : ∀ X0 : G, (k (τ (M.op X0 (σ x))) x) = (τ (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e72 (M.op X0 (σ x)) x
               have i₂ := b5e11168 X0
               grind)
            | exact superpose b5e11168 b5e72
            | exact resolve b5e72 b5e11168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72 b5e11168
          have b5e11208 : ∀ X0 : G, x = (k (τ (M.op X0 (σ x))) x) := by
            intro X0
            first
            | (have i₁ := b5e11188 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e11188
            | exact resolve b5e11188 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11188
          have b5e11381 : ∀ X0 : G, x = (k (τ (σ (k X0 x))) x) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e11208 (σ X0)
               have i₂ := b5e397 x X0
               grind)
            | exact superpose b5e397 b5e11208
            | (have j1 := b5e397 x X0
               grind)
            | exact resolve b5e11208 b5e397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e397 b5e11208
          have b5e11414 : ∀ X0 : G, x = (k (k X0 x) x) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e11381 X0
               have i₂ := b5e14 (k X0 x)
               grind)
            | exact superpose b5e14 b5e11381
            | (have j0 := b5e11381 X0
               grind)
            | exact resolve b5e11381 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11381
          have b5e13402 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2052 (τ X0) (τ X1)
               have i₂ := b5e285 X1 X0
               grind)
            | exact superpose b5e285 b5e2052
            | (have j0 := b5e2052 (τ X1) (τ (k X0 X1))
               grind)
            | exact resolve b5e2052 b5e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e285 b5e2052
          have b5e13513 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13402 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e13402
            | (have j0 := b5e13402 X0 X1
               grind)
            | exact resolve b5e13402 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13402
          have b5e13523 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13513 X0 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e13513
            | (have j0 := b5e13513 X0 X1
               grind)
            | exact resolve b5e13513 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13513
          have b5e13524 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 (k X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13523 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e13523
            | (have j0 := b5e13523 X0 X1
               grind)
            | exact resolve b5e13523 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13523
          have b5e13525 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13524 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e13524
            | (have j0 := b5e13524 X0 X1
               grind)
            | exact resolve b5e13524 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13524
          have b5e14018 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e11129 X0 (τ (M.op (σ (M.op X0 (σ x))) (σ (M.op X0 (σ x)))))
               have i₂ := b5e643 (M.op X0 (σ x))
               grind)
            | exact superpose b5e643 b5e11129
            | exact resolve b5e11129 b5e643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e643 b5e11129
          have b5e14450 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b5e14018 (σ (M.op x x))
               have i₂ := b5e828 x
               grind)
            | exact superpose b5e828 b5e14018
            | exact resolve b5e14018 b5e828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e828 b5e14018
          have b5e14744 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b5e29 (σ y) (σ (M.op x x))
               have i₂ := b5e14450
               grind)
            | exact superpose b5e14450 b5e29
            | exact resolve b5e29 b5e14450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14450
          have b5e15292 : ∀ X0 X1 : G, (k X1 X0) = (M.op (k X1 X0) X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X0 (k X1 X0)
               have i₂ := b5e13525 X1 X0
               grind)
            | exact superpose b5e13525 b5e29
            | (have j1 := b5e13525 (k X1 X0) X0
               grind)
            | exact resolve b5e29 b5e13525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13525
          have b5e32928 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (M.op x X0) = (k y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e2863 y x x
               have i₂ := b5e31
               grind)
            | exact superpose b5e31 b5e2863
            | exact resolve b5e2863 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2863
          have b5e33229 : ∀ X0 : G, (M.op x X0) = (k y (M.op x X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e32928 X0
               have i₂ := b5e4351
               grind)
            | exact superpose b5e4351 b5e32928
            | (have j0 := b5e32928 X0
               grind)
            | exact resolve b5e32928 b5e4351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4351 b5e32928
          have b5e46012 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) ∨ x = (k y x) := by
            intro X0
            first
            | (have i₁ := b5e33229 (M.op X0 x)
               have i₂ := b5e29 X0 x
               grind)
            | exact superpose b5e29 b5e33229
            | (have j0 := b5e33229 (M.op X0 x)
               grind)
            | exact resolve b5e33229 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33229
          have b5e133082 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = (k (M.op (M.op X0 X1) X2) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e4770 X1 X3 X0 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4770
          have b5e166612 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X0) ∨ (M.op X1 X2) = (k (M.op (M.op X0 X1) X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e133 X0 X1 X0 X2
               have i₂ := b5e1270 X0 X1 (M.op X0 X1) X0
               grind)
            | exact superpose b5e1270 b5e133
            | (have j0 := b5e133 X0 X1 X0 X2
               grind)
            | exact resolve b5e133 b5e1270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133 b5e1270
          have b5e166817 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op (M.op X0 X1) X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e166612 X0 X1 X2
               have j1 := b5e133082 X0 X1 X0 X2
               grind)
            | (have r₁ := b5e166612 X2 X1 x
               have r₂ := b5e133082 X2 X1 X2 x
               grind)
            | exact resolve b5e166612 b5e133082
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133082 b5e166612
          have b5e189759 : ∀ X0 X3 : G, (k (M.op (M.op X3 X0) X3) X0) = X0 := by
            intro X0 X3
            first
            | (have i₁ := b5e166817 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e166817
            | exact resolve b5e166817 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166817
          have b5e191411 : x = (k (M.op y x) x) ∨ x = (k y x) := by
            first
            | (have i₁ := b5e189759 x y
               have i₂ := b5e46012 y
               grind)
            | exact superpose b5e46012 b5e189759
            | exact resolve b5e189759 b5e46012
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46012 b5e189759
          have b5e191470 : x = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b5e191411
               have i₂ := b5e31
               grind)
            | exact superpose b5e31 b5e191411
            | exact resolve b5e191411 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e191411
          have b5e191471 : x = (k y x) := by grind
          clear b5e191470
          have b5e3155944 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e11414 y
               have i₂ := b5e191471
               grind)
            | exact superpose b5e191471 b5e11414
            | (have j0 := b5e11414 y
               grind)
            | exact resolve b5e11414 b5e191471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11414 b5e191471
          have b5e3163018 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e29 (σ y) (σ x)
               have i₂ := b5e3155944
               grind)
            | exact superpose b5e3155944 b5e29
            | exact resolve b5e29 b5e3155944
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e3155944
          have b5e3163023 : x = (k x x) := by
            first
            | (have r₁ := b5e3163018
               have r₂ := b5e24
               grind)
            | exact resolve b5e3163018 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3163018
          have b5e3170231 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e15292 x x
               have i₂ := b5e3163023
               grind)
            | exact superpose b5e3163023 b5e15292
            | (have j0 := b5e15292 x x
               grind)
            | exact resolve b5e15292 b5e3163023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15292 b5e3163023
          have b5e3170233 : x = (M.op x x) := by grind
          clear b5e3170231
          have b5e3176634 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e14744
               have i₂ := b5e3170233
               grind)
            | exact superpose b5e3170233 b5e14744
            | exact resolve b5e14744 b5e3170233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14744 b5e3170233
          have b5e3176985 : False := by grind
          exact b5e3176985
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
        have b6e56 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
        have b6e66 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e56
        have b6e69 : y = (M.op x x) := by
          first
          | (have r₁ := b6e66
             have r₂ := b6e21
             grind)
          | exact resolve b6e66 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e72 : False := by grind
        exact b6e72
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
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
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op (M.op x (M.op X0 X1)) x)
               have i₂ := b7e13 (M.op X0 X1) x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e32 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e29 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X1 X0) X0 X2
               have i₂ := b7e29 X1 X0
               grind)
            | exact superpose b7e29 b7e13
            | exact resolve b7e13 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e44 : (σ y) = (σ (k x y)) := by
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
          have b7e47 : (k x y) = (τ (σ y)) := by
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
          have b7e48 : y = (k x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e47
            | exact resolve b7e47 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e57 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e29 X1 X1
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e29 X0 X1
               have i₂ := b7e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b7e18 b7e29
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e29 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e65 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e66 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e21
               grind)
            | exact resolve b7e65 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : y = (M.op x y) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e22
               grind)
            | exact resolve b7e66 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e78 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e26
            | exact resolve b7e26 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e81 : y = (M.op y y) := by
            first
            | (have i₁ := b7e29 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e29
            | exact resolve b7e29 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e84 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          clear b7e30
          have b7e89 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e84 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e84
            | exact resolve b7e84 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e223 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ y) (σ x)
               have i₂ := b7e32
               grind)
            | exact superpose b7e32 b7e17
            | (have j0 := b7e17 (σ y) (σ x)
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e32
               grind)
            | exact resolve b7e17 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e231 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e223
          have b7e232 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e231
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e231
            | exact resolve b7e231 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e231
          have b7e504 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b7e35 x X0 y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e35
            | exact resolve b7e35 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e68
          have b7e554 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e89 X0
               have i₂ := b7e61 (σ (M.op (τ X0) (τ X0))) X0
               grind)
            | exact superpose b7e61 b7e89
            | (have j1 := b7e61 (σ (M.op (τ X0) (τ X0))) X0
               grind)
            | exact resolve b7e89 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e563 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have j0 := b7e554 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e554
          have b7e860 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e563 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e563
            | exact resolve b7e563 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e563
          have b7e1026 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e860 y
               have i₂ := b7e81
               grind)
            | exact superpose b7e81 b7e860
            | exact resolve b7e860 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e860
          have b7e9562 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1026
               have i₂ := b7e232
               grind)
            | exact superpose b7e232 b7e1026
            | exact resolve b7e1026 b7e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e232 b7e1026
          have b7e9635 : (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b7e9562
               have r₂ := b7e78
               grind)
            | exact resolve b7e9562 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e9562
          have b7e9650 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e9635
               grind)
            | exact superpose b7e9635 b7e14
            | exact resolve b7e14 b7e9635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9635
          have b7e9698 : x = (k y x) := by
            first
            | (have i₁ := b7e9650
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e9650
            | exact resolve b7e9650 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9650
          have b7e9786 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e61 x y
               have i₂ := b7e9698
               grind)
            | exact superpose b7e9698 b7e61
            | (have j0 := b7e61 x y
               grind)
            | exact resolve b7e61 b7e9698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61 b7e9698
          have b7e9920 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e29 y x
               have i₂ := b7e9786
               grind)
            | exact superpose b7e9786 b7e29
            | exact resolve b7e29 b7e9786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e9786
          have b7e9956 : x = (M.op y x) := by
            first
            | (have r₁ := b7e9920
               have r₂ := b7e22
               grind)
            | exact resolve b7e9920 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9920
          have b7e10076 : x = (M.op x y) := by
            first
            | (have i₁ := b7e504 y
               have i₂ := b7e9956
               grind)
            | exact superpose b7e9956 b7e504
            | exact resolve b7e504 b7e9956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e504 b7e9956
          have b7e10119 : False := by grind
          exact b7e10119
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
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e289 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e20
            | (have j1 := b8e63 x y
               grind)
            | exact resolve b8e20 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e344 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e289
               have r₂ := b8e23
               grind)
            | exact resolve b8e289 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e289
          have b8e349 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e344
               have r₂ := b8e24
               grind)
            | exact resolve b8e344 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e344
          have b8e350 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e349
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e349
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e349 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e349
          have b8e351 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e350
          have b8e352 : x = (M.op x y) := by
            first
            | (have r₁ := b8e351
               have r₂ := b8e21
               grind)
            | exact resolve b8e351 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e351
          have b8e353 : False := by grind
          exact b8e353

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
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
      have b0e29 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
      have b0e30 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
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
      have b0e36 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e30 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e37 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e29
        | exact resolve b0e29 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e38 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e36 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e37 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e52 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e38 (σ x)
           grind)
        | exact superpose b0e38 b0e18
        | exact resolve b0e18 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e55 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e52
           have i₂ := b0e39 x
           grind)
        | exact superpose b0e39 b0e52
        | exact resolve b0e52 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e52
      have b0e56 : False := by grind
      exact b0e56
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e27 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
        have b1e34 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e27 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e27
          | exact resolve b1e27 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e35 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e34 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e34
          | exact resolve b1e34 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e45 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e46 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e21
             grind)
          | exact resolve b1e45 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b1e48 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e24 x
             grind)
          | exact superpose b1e24 b1e47
          | exact resolve b1e47 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e47
        have b1e49 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e19
          | exact resolve b1e19 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e55 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e35 x
             grind)
          | exact superpose b1e35 b1e49
          | exact resolve b1e49 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e49
        have b1e56 : False := by grind
        exact b1e56
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e27 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
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
        have b2e33 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e27 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e27
          | exact resolve b2e27 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e34 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e33 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e33
          | exact resolve b2e33 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op y X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 y
             have i₂ := b2e34 (M.op X0 (M.op y X0))
             grind)
          | exact superpose b2e34 b2e12
          | exact resolve b2e12 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b2e16 y X0
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e16
          | (have j0 := b2e16 y X0
             grind)
          | (have r₁ := b2e16 y X0
             have r₂ := b2e34 X0
             grind)
          | exact resolve b2e16 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e94 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e24 (τ X0)
             grind)
          | exact superpose b2e24 b2e25
          | exact resolve b2e25 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e25
        have b2e99 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e94 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e94
          | exact resolve b2e94 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e782 : (σ y) ≠ (σ y) ∨ (M.op y (σ y)) = (k y (σ y)) := by
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
        have b2e789 : (M.op y (σ y)) = (k y (σ y)) := by grind
        clear b2e782
        have b2e795 : y = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e789
             have i₂ := b2e99 y
             grind)
          | exact superpose b2e99 b2e789
          | exact resolve b2e789 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99 b2e789
        have b2e802 : ∀ X0 : G, (M.op X0 (M.op (σ y) y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e37 (σ y) X0
             have i₂ := b2e795
             grind)
          | exact superpose b2e795 b2e37
          | exact resolve b2e37 b2e795
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e795
        have b2e821 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e802 X0
             have i₂ := b2e34 (σ y)
             grind)
          | exact superpose b2e34 b2e802
          | exact resolve b2e802 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e802
        have b2e903 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e821 (σ y)
             grind)
          | exact superpose b2e821 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e821 (σ y)
             grind)
          | exact resolve b2e21 b2e821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e821
        have b2e909 : False := by grind
        exact b2e909
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b3e24 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e24 (σ X0)
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e28 X0
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e49 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
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
        have b3e54 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
        clear b3e49
        have b3e55 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e54
             have r₂ := b3e20
             grind)
          | exact resolve b3e54 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e56 : x = (M.op x y) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e55
          | exact resolve b3e55 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e55
        have b3e58 : ∀ X0 : G, (M.op X0 (M.op (M.op y x) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e12
          | exact resolve b3e12 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e60 : ∀ X0 : G, (M.op X0 (M.op y x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e58
          | exact resolve b3e58 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e62 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e60 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e60
          | exact resolve b3e60 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e78 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e62 y
             grind)
          | exact superpose b3e62 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e62 y
             grind)
          | exact resolve b3e20 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e79 : False := by grind
        exact b3e79
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b4e17 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e40
          have b4e46 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
          clear b4e39
          have b4e47 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e45
               have r₂ := b4e23
               grind)
            | exact resolve b4e45 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e48 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e46
               have r₂ := b4e21
               grind)
            | exact resolve b4e46 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e49 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e47
            | exact resolve b4e47 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e50 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e49
               have i₂ := b4e48
               grind)
            | exact superpose b4e48 b4e49
            | exact resolve b4e49 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e49
          have b4e51 : False := by grind
          exact b4e51
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = X0 := by
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
          have b5e29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
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
          have b5e33 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y (M.op x y)
               have i₂ := b5e27 y
               grind)
            | exact superpose b5e27 b5e13
            | exact resolve b5e13 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e93 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29 x X0 y
               have i₂ := b5e33 x
               grind)
            | exact superpose b5e33 b5e29
            | exact resolve b5e29 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e101 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e93 x
               grind)
            | exact superpose b5e93 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e93 x
               grind)
            | exact resolve b5e16 b5e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93
          have b5e107 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b5e101 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101
          have b5e643 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e47 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e645 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e643 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e643
          have b5e3138 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e645 x
               have i₂ := b5e107 x
               grind)
            | exact superpose b5e107 b5e645
            | (have j0 := b5e645 x
               grind)
            | exact resolve b5e645 b5e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e107 b5e645
          have b5e3144 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e3138
          have b5e3202 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29 (σ x) X0 (σ x)
               have i₂ := b5e3144
               grind)
            | exact superpose b5e3144 b5e29
            | exact resolve b5e29 b5e3144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e3227 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e3202 X0
               have i₂ := b5e3144
               grind)
            | exact superpose b5e3144 b5e3202
            | exact resolve b5e3202 b5e3144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3202
          have b5e3242 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e3227 X0
               have i₂ := b5e3144
               grind)
            | exact superpose b5e3144 b5e3227
            | exact resolve b5e3227 b5e3144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3144 b5e3227
          have b5e3534 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3242 (σ y)
               grind)
            | exact superpose b5e3242 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e3242 (σ y)
               grind)
            | exact resolve b5e24 b5e3242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3242
          have b5e3546 : False := by grind
          exact b5e3546
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e24 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e28 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e57 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e63 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b6e57 X0
             grind)
          | (have r₁ := b6e57 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e57 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e57 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e902 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b6e63 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e960 : y = (M.op y y) := by
          first
          | (have j0 := b6e902 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e902
        have b6e961 : False := by grind
        exact b6e961
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
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
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
          have b7e37 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e40 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e40
               have r₂ := b7e23
               grind)
            | exact resolve b7e40 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e41
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e41
            | exact resolve b7e41 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e26 X1 X0
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X0)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e29 (σ y) X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
               have i₂ := b7e29 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b7e29 b7e16
            | (have j0 := b7e16 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | (have r₁ := b7e16 X0 (M.op X0 (M.op X2 (M.op X0 X2)))
               have r₂ := b7e29 X0 (M.op X0 (M.op X2 (M.op X0 X2))) X2
               grind)
            | exact resolve b7e16 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e73 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e79 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ (k x y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e65 X0
               have i₂ := b7e42
               grind)
            | exact superpose b7e42 b7e65
            | exact resolve b7e65 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e268 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ y) (σ (k x y))))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e78 (σ x) (σ y) X0
               have i₂ := b7e42
               grind)
            | exact superpose b7e42 b7e78
            | exact resolve b7e78 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42 b7e78
          have b7e289 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e268 X0
               have i₂ := b7e79 (σ x)
               grind)
            | exact superpose b7e79 b7e268
            | exact resolve b7e268 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e268
          have b7e329 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e48 X0 (σ x)
               have i₂ := b7e289 (σ X0)
               grind)
            | exact superpose b7e289 b7e48
            | exact resolve b7e48 b7e289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e289
          have b7e332 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e329 X0
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e329
            | exact resolve b7e329 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e329
          have b7e333 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e332 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e332
            | exact resolve b7e332 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e332
          have b7e403 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ x)) := by
            intro X0
            first
            | (have i₁ := b7e48 X0 x
               have i₂ := b7e333 (σ X0)
               grind)
            | exact superpose b7e333 b7e48
            | exact resolve b7e48 b7e333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e333
          have b7e406 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e403 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e403
            | exact resolve b7e403 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e403
          have b7e520 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e52 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e522 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e520 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e520
          have b7e4213 : (σ (τ x)) ≠ (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by
            first
            | (have i₁ := b7e522 (τ x)
               have i₂ := b7e406 (τ x)
               grind)
            | exact superpose b7e406 b7e522
            | (have j0 := b7e522 (τ x)
               grind)
            | exact resolve b7e522 b7e406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e406 b7e522
          have b7e4239 : (σ (τ x)) = (M.op (σ (τ x)) (σ (τ x))) := by grind
          clear b7e4213
          have b7e4277 : x = (M.op x x) := by
            first
            | (have i₁ := b7e4239
               have i₂ := b7e15 x
               grind)
            | exact superpose b7e15 b7e4239
            | exact resolve b7e4239 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4239
          have b7e4288 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e29 x X0 x
               have i₂ := b7e4277
               grind)
            | exact superpose b7e4277 b7e29
            | exact resolve b7e29 b7e4277
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e4314 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e4288 X0
               have i₂ := b7e4277
               grind)
            | exact superpose b7e4277 b7e4288
            | exact resolve b7e4288 b7e4277
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4288
          have b7e4330 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e4314 X0
               have i₂ := b7e4277
               grind)
            | exact superpose b7e4277 b7e4314
            | exact resolve b7e4314 b7e4277
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4277 b7e4314
          have b7e4644 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e4330 y
               grind)
            | exact superpose b7e4330 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e4330 y
               grind)
            | exact resolve b7e22 b7e4330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4330
          have b7e4645 : False := by grind
          exact b7e4645
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b8e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
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
          have b8e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e25 X0 X1
               grind)
            | exact superpose b8e25 b8e14
            | exact resolve b8e14 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e26 X1 X0
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e52 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e52 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e55 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e35 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e35
            | exact resolve b8e35 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e66 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 X0 X1 X0
               have i₂ := b8e18 X2 X0
               grind)
            | exact superpose b8e18 b8e28
            | (have j1 := b8e18 X2 X0
               grind)
            | exact resolve b8e28 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
               have i₂ := b8e28 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
               grind)
            | exact superpose b8e28 b8e16
            | (have j0 := b8e16 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 (M.op X2 (M.op X0 X2)))
               have r₂ := b8e28 X0 (M.op X0 (M.op X2 (M.op X0 X2))) X2
               grind)
            | exact resolve b8e16 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e70 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e158 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e43 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
               have i₂ := b8e75 X1 X2 (σ X0)
               grind)
            | exact superpose b8e75 b8e43
            | exact resolve b8e43 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e162 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e158 X0 X1 X2
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e158
            | exact resolve b8e158 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158
          have b8e555 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e47 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e557 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e555 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e555
          have b8e1754 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e557 (M.op X0 (M.op X1 (M.op X0 X1)))
               have i₂ := b8e75 X0 X1 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | exact superpose b8e75 b8e557
            | (have j0 := b8e557 (M.op X0 (M.op X1 (M.op X0 X1)))
               grind)
            | exact resolve b8e557 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e1774 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e557 (τ X0)
               have i₂ := b8e26 X0 (τ X0)
               grind)
            | exact superpose b8e26 b8e557
            | (have j0 := b8e557 (τ X0)
               grind)
            | exact resolve b8e557 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e557
          have b8e1789 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
            intro X0 X1
            first
            | (have j0 := b8e1754 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1754
          have b8e1795 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e1774 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1774
            | (have j0 := b8e1774 X0
               grind)
            | exact resolve b8e1774 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1774
          have b8e1805 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e1795 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1795
            | (have j0 := b8e1795 X0
               grind)
            | exact resolve b8e1795 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1795
          have b8e1878 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e1805 (τ X0)
               have i₂ := b8e55 X0 X0
               grind)
            | exact superpose b8e55 b8e1805
            | (have j0 := b8e1805 (τ X0)
               grind)
            | exact resolve b8e1805 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55 b8e1805
          have b8e3672 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e1878 (σ y)
               have i₂ := b8e53 (σ y)
               grind)
            | exact superpose b8e53 b8e1878
            | (have j0 := b8e1878 (σ y)
               have j1 := b8e53 (σ y)
               grind)
            | exact resolve b8e1878 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53 b8e1878
          have b8e3718 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
            first
            | (have r₁ := b8e3672
               have r₂ := b8e23
               grind)
            | exact resolve b8e3672 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3672
          have b8e3733 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
            first
            | (have i₁ := b8e3718
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e3718
            | exact resolve b8e3718 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3718
          have b8e3735 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b8e3733
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e3733
            | exact resolve b8e3733 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3733
          have b8e3736 : y ≠ (τ (M.op (σ y) (σ y))) := by
            first
            | (have r₁ := b8e3735
               have r₂ := b8e21
               grind)
            | exact resolve b8e3735 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3735
          have b8e4050 : y ≠ (τ (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e3736
               have i₂ := b8e47 y y
               grind)
            | exact superpose b8e47 b8e3736
            | (have j1 := b8e47 y y
               grind)
            | exact resolve b8e3736 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e3736
          have b8e4053 : y ≠ (τ (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b8e4050
          have b8e4054 : y ≠ (τ (σ (k y y))) := by
            first
            | (have r₁ := b8e4053
               have r₂ := b8e23
               grind)
            | exact resolve b8e4053 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4053
          have b8e4056 : y ≠ (k y y) := by
            first
            | (have i₁ := b8e4054
               have i₂ := b8e14 (k y y)
               grind)
            | exact superpose b8e14 b8e4054
            | exact resolve b8e4054 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4054
          have b8e6367 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 X0 X1 X0
               have i₂ := b8e66 X0 X0 X2
               grind)
            | exact superpose b8e66 b8e28
            | (have j1 := b8e66 X0 X1 X2
               grind)
            | exact resolve b8e28 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e20501 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e6367 (σ x) (σ y) X0
               grind)
            | exact superpose b8e6367 b8e24
            | (have j1 := b8e6367 (σ x) x X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e6367 (σ x) (σ y) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e6367 (σ y) x (σ x)
               grind)
            | exact resolve b8e24 b8e6367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e20503 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e20501 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20501
          have b8e21050 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e20503 (σ X0)
               grind)
            | exact superpose b8e20503 b8e19
            | (have j1 := b8e20503 (σ X0)
               grind)
            | exact resolve b8e19 b8e20503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20503
          have b8e48232 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e21050 y
               grind)
            | exact superpose b8e21050 b8e20
            | (have j1 := b8e21050 y
               grind)
            | exact resolve b8e20 b8e21050
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21050
          have b8e50630 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e48232
               have i₂ := b8e6367 x X0 y
               grind)
            | exact superpose b8e6367 b8e48232
            | (have j1 := b8e6367 x X0 y
               grind)
            | exact resolve b8e48232 b8e6367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6367 b8e48232
          have b8e50631 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e50630 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50630
          have b8e61049 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (M.op X1 x) = X1 ∨ x = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e28 (σ x) X0 (σ y)
               have i₂ := b8e50631 X1
               grind)
            | exact superpose b8e50631 b8e28
            | (have j1 := b8e50631 X1
               grind)
            | exact resolve b8e28 b8e50631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50631
          have b8e147305 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (M.op X1 x) = X1 ∨ x = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e162 X0 (σ y) (σ x)
               have i₂ := b8e61049 (σ y) X1
               grind)
            | exact superpose b8e61049 b8e162
            | (have j1 := b8e61049 X0 X1
               grind)
            | exact resolve b8e162 b8e61049
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162 b8e61049
          have b8e147421 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op X1 x) = X1 ∨ x = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e147305 X0 X1
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e147305
            | (have j0 := b8e147305 X0 X1
               grind)
            | exact resolve b8e147305 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147305
          have b8e147539 : ∀ X0 : G, y ≠ y ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e4056
               have i₂ := b8e147421 y X0
               grind)
            | exact superpose b8e147421 b8e4056
            | (have j1 := b8e147421 X0 X0
               grind)
            | (have r₁ := b8e4056
               have r₂ := b8e147421 y x
               grind)
            | exact resolve b8e4056 b8e147421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4056 b8e147421
          have b8e147694 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e147539 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147539
          have b8e148571 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ (M.op X1 x) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e28 x X0 y
               have i₂ := b8e147694 X1
               grind)
            | exact superpose b8e147694 b8e28
            | (have j1 := b8e147694 X1
               grind)
            | exact resolve b8e28 b8e147694
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28 b8e147694
          have b8e154044 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e1789 y x
               have i₂ := b8e148571 y x
               grind)
            | exact superpose b8e148571 b8e1789
            | (have j1 := b8e148571 X0 X0
               grind)
            | exact resolve b8e1789 b8e148571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1789 b8e148571
          have b8e154501 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b8e154044 X0
               grind)
            | (have r₁ := b8e154044 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e154044 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154044
          have b8e155570 : y ≠ y := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e154501 y
               grind)
            | exact superpose b8e154501 b8e22
            | (have r₁ := b8e22
               have r₂ := b8e154501 y
               grind)
            | exact resolve b8e22 b8e154501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154501
          have b8e155571 : False := by grind
          exact b8e155571

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation1256 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1256 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e80 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e85 : False := by grind
      exact b0e85
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : False := by grind
        exact b1e26
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : False := by grind
        exact b2e26
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
               have i₂ := b4e13 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b4e36 X0 x x X3
               have i₂ := b4e13 (M.op X0 X0) x x
               grind)
            | exact superpose b4e13 b4e36
            | exact resolve b4e36 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e39 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e37 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e37 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e78 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e40 (σ x)
               grind)
            | exact superpose b4e40 b4e20
            | exact resolve b4e20 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e80 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e78
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e78
            | exact resolve b4e78 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e78
          have b4e81 : False := by grind
          exact b4e81
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e118 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e123 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e118
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e118
            | exact resolve b5e118 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e124 : False := by grind
          exact b5e124
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
               have i₂ := b7e13 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b7e35 X0 x x X3
               have i₂ := b7e13 (M.op X0 X0) x x
               grind)
            | exact superpose b7e13 b7e35
            | exact resolve b7e35 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e38 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e36 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e97 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e38 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e38
            | exact resolve b7e38 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e38
          have b7e105 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e97
               grind)
            | exact superpose b7e97 b7e14
            | exact resolve b7e14 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e106 : y = (M.op y y) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e105
            | exact resolve b7e105 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e110 : False := by grind
          exact b7e110
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e56 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e56
            | (have j0 := b8e56 X0 X1
               grind)
            | exact resolve b8e56 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e83 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e299 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e20
            | (have j1 := b8e65 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e317 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e299
               have r₂ := b8e83
               grind)
            | exact resolve b8e299 b8e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83 b8e299
          have b8e327 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e317
               have r₂ := b8e23
               grind)
            | exact resolve b8e317 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e317
          have b8e340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e327
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e327
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e327
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e327
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e327 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e327
          have b8e341 : y = (M.op y y) ∨ x = y := by grind
          clear b8e340
          have b8e343 : x = y := by
            first
            | (have r₁ := b8e341
               have r₂ := b8e22
               grind)
            | exact resolve b8e341 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e341
          have b8e346 : False := by grind
          exact b8e346

/-- `Equation310`: `x ◇ x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation310 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law310 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law310.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e30
      have b0e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e31
      have b0e79 : False := by grind
      exact b0e79
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : False := by grind
        exact b1e28
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : False := by grind
        exact b2e28
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e28 X0
               grind)
            | (have i₁ := b4e13 X0 x
               have i₂ := b4e28 x
               grind)
            | exact superpose b4e28 b4e13
            | exact resolve b4e13 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e28 X0
               grind)
            | (have i₁ := b4e13 x X1
               have i₂ := b4e28 x
               grind)
            | exact superpose b4e28 b4e13
            | exact resolve b4e13 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e39
          have b4e42 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b4e40 X0
               have i₂ := b4e28 (σ X0)
               grind)
            | exact superpose b4e28 b4e40
            | exact resolve b4e40 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) x) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e70 X0 X1
               have i₂ := b4e28 (σ X0)
               grind)
            | exact superpose b4e28 b4e70
            | (have j0 := b4e70 X0 X1
               grind)
            | exact resolve b4e70 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e95 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e28 X0
               grind)
            | (have i₁ := b4e42 x
               have i₂ := b4e28 x
               grind)
            | exact superpose b4e28 b4e42
            | exact resolve b4e42 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0
               have i₂ := b4e34 X1 X0
               grind)
            | (have i₁ := b4e28 (M.op X0 x)
               have i₂ := b4e34 X0 (M.op X0 x)
               grind)
            | exact superpose b4e34 b4e28
            | exact resolve b4e28 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e34
          have b4e198 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e95 X0
               grind)
            | exact superpose b4e95 b4e42
            | exact resolve b4e42 b4e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95
          have b4e610 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e121 X1 (σ X0)
               have i₂ := b4e42 X0
               grind)
            | exact superpose b4e42 b4e121
            | exact resolve b4e121 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e803 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e82 x y
               grind)
            | exact superpose b4e82 b4e20
            | (have j1 := b4e82 x y
               grind)
            | exact resolve b4e20 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e810 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) x) := by
            first
            | (have r₁ := b4e803
               have r₂ := b4e23
               grind)
            | exact resolve b4e803 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e803
          have b4e831 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e810
               have i₂ := b4e42 x
               grind)
            | exact superpose b4e42 b4e810
            | exact resolve b4e810 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e810
          have b4e3460 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b4e831
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e831
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e831
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e831
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e831 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e831
          have b4e3461 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by grind
          clear b4e3460
          have b4e3467 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b4e3461
               have r₂ := b4e21
               grind)
            | exact resolve b4e3461 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3461
          have b4e7891 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e3467
               grind)
            | exact superpose b4e3467 b4e14
            | exact resolve b4e14 b4e3467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3467
          have b4e7930 : y = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e7891
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e7891
            | exact resolve b4e7891 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7891
          have b4e7931 : y = (M.op x x) := by grind
          clear b4e7930
          have b4e8220 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e35 X0 x
               have i₂ := b4e7931
               grind)
            | exact superpose b4e7931 b4e35
            | exact resolve b4e35 b4e7931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e8224 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e610 x X0
               have i₂ := b4e7931
               grind)
            | exact superpose b4e7931 b4e610
            | exact resolve b4e610 b4e7931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e610 b4e7931
          have b4e10021 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e198 X0
               have i₂ := b4e8220 X0
               grind)
            | exact superpose b4e8220 b4e198
            | exact resolve b4e198 b4e8220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e198 b4e8220
          have b4e14138 : (σ (M.op x y)) ≠ (M.op (σ x) x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e8224 (σ x)
               grind)
            | exact superpose b4e8224 b4e20
            | exact resolve b4e20 b4e8224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8224
          have b4e14155 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e14138
               have i₂ := b4e42 x
               grind)
            | exact superpose b4e42 b4e14138
            | exact resolve b4e14138 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e14138
          have b4e14174 : False := by grind
          exact b4e14174
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : (σ x) ≠ (M.op (σ y) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e28 (σ y)
               grind)
            | exact superpose b5e28 b5e24
            | exact resolve b5e24 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e37
          have b5e40 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b5e38 X0
               have i₂ := b5e28 (σ X0)
               grind)
            | exact superpose b5e28 b5e38
            | exact resolve b5e38 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e38
          have b5e47 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e31
               have i₂ := b5e40 y
               grind)
            | exact superpose b5e40 b5e31
            | exact resolve b5e31 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e40
          have b5e48 : (σ x) ≠ (σ x) := by
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
          have b5e49 : False := by grind
          exact b5e49
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : x = y := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e36
          have b7e118 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e37 y
               grind)
            | exact superpose b7e37 b7e24
            | exact resolve b7e24 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e139 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e118
               grind)
            | exact superpose b7e118 b7e14
            | exact resolve b7e14 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e140 : x = (M.op y y) := by
            first
            | (have i₁ := b7e139
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e139
            | exact resolve b7e139 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e144 : False := by grind
          exact b7e144
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e32
          have b8e36 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e29
          have b8e40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e36 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e36
            | exact resolve b8e36 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e40
          have b8e61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e61 X0 X1
               have i₂ := b8e33 X0
               grind)
            | exact superpose b8e33 b8e61
            | (have j0 := b8e61 X0 X1
               grind)
            | exact resolve b8e61 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e79 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0)
               have i₂ := b8e33 X0
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) X1
               have i₂ := b8e33 X0
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e173 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e41 X0
               have i₂ := b8e13 (τ X0) X1
               grind)
            | exact superpose b8e13 b8e41
            | exact resolve b8e41 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e465 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e69 x y
               grind)
            | exact superpose b8e69 b8e20
            | (have j1 := b8e69 x y
               grind)
            | exact resolve b8e20 b8e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e508 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e465
               have r₂ := b8e23
               grind)
            | exact resolve b8e465 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e465
          have b8e875 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op (τ (σ X0)) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 X0
               have i₂ := b8e173 (σ X0) X1
               grind)
            | exact superpose b8e173 b8e33
            | exact resolve b8e33 b8e173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e173
          have b8e888 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e875 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e875
            | exact resolve b8e875 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e875
          have b8e5751 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e508
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e508
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e508
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e508
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e508 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e508
          have b8e5753 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by grind
          clear b8e5751
          have b8e5758 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b8e5753
               have r₂ := b8e21
               grind)
            | exact resolve b8e5753 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5753
          have b8e5772 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e5758
               grind)
            | exact superpose b8e5758 b8e14
            | exact resolve b8e14 b8e5758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5758
          have b8e5812 : y = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e5772
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e5772
            | exact resolve b8e5772 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5772
          have b8e5813 : y = (M.op x x) := by grind
          clear b8e5812
          have b8e5894 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x
               have i₂ := b8e5813
               grind)
            | exact superpose b8e5813 b8e13
            | exact resolve b8e13 b8e5813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5903 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e79 x X0
               have i₂ := b8e5813
               grind)
            | exact superpose b8e5813 b8e79
            | exact resolve b8e79 b8e5813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e5904 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b8e80 X0 x
               have i₂ := b8e5813
               grind)
            | exact superpose b8e5813 b8e80
            | exact resolve b8e80 b8e5813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e5931 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b8e888 X0 x
               have i₂ := b8e5813
               grind)
            | exact superpose b8e5813 b8e888
            | exact resolve b8e888 b8e5813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e888 b8e5813
          have b8e7833 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e5894 X0
               have i₂ := b8e5903 X0
               grind)
            | (have i₁ := b8e5894 (σ y)
               have i₂ := b8e5903 (σ y)
               grind)
            | exact superpose b8e5903 b8e5894
            | exact resolve b8e5894 b8e5903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5894 b8e5903
          have b8e9764 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e7833 (σ x)
               grind)
            | exact superpose b8e7833 b8e20
            | exact resolve b8e20 b8e7833
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7833
          have b8e9770 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e9764
               have i₂ := b8e5904 x
               grind)
            | exact superpose b8e5904 b8e9764
            | exact resolve b8e9764 b8e5904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5904 b8e9764
          have b8e9802 : False := by grind
          exact b8e9802

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation327 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law327 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e29
      have b0e73 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e30
      have b0e77 : False := by grind
      exact b0e77
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : False := by grind
        exact b1e28
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : False := by grind
        exact b2e28
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
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
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
          have b4e28 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e28 (σ x)
               grind)
            | exact superpose b4e28 b4e20
            | exact resolve b4e20 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e39 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e40 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e27 x
               grind)
            | exact superpose b4e27 b4e39
            | exact resolve b4e39 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e39
          have b4e41 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e40
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e40
            | exact resolve b4e40 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e42 : False := by grind
          exact b4e42
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e33
          have b5e81 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e34 x
               grind)
            | exact superpose b5e34 b5e24
            | exact resolve b5e24 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e86 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e81
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e81
            | exact resolve b5e81 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e87 : False := by grind
          exact b5e87
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : x = y := by
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
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e33
          have b7e105 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e34 x
               grind)
            | exact superpose b7e34 b7e24
            | exact resolve b7e24 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e131 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e105
               grind)
            | exact superpose b7e105 b7e14
            | exact resolve b7e14 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e132 : y = (M.op x x) := by
            first
            | (have i₁ := b7e131
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e131
            | exact resolve b7e131 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131
          have b7e136 : False := by grind
          exact b7e136
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e31
          have b8e59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e59 X0 X1
               have i₂ := b8e32 X1
               grind)
            | exact superpose b8e32 b8e59
            | (have j0 := b8e59 X0 X1
               grind)
            | exact resolve b8e59 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e76 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e32 X0
               grind)
            | exact superpose b8e32 b8e13
            | exact resolve b8e13 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e270 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e68 x y
               grind)
            | exact superpose b8e68 b8e20
            | (have j1 := b8e68 x y
               grind)
            | exact resolve b8e20 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e312 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e270
               have r₂ := b8e23
               grind)
            | exact resolve b8e270 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e270
          have b8e1049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e312
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e312
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e312
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e312
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e312 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e312
          have b8e1051 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b8e1049
          have b8e1056 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b8e1051
               have r₂ := b8e21
               grind)
            | exact resolve b8e1051 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1051
          have b8e1064 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e1056
               grind)
            | exact superpose b8e1056 b8e14
            | exact resolve b8e14 b8e1056
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1056
          have b8e1095 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e1064
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e1064
            | exact resolve b8e1064 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1064
          have b8e1096 : x = (M.op y y) := by grind
          clear b8e1095
          have b8e1194 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e76 y X0
               have i₂ := b8e1096
               grind)
            | exact superpose b8e1096 b8e76
            | exact resolve b8e76 b8e1096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e1198 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 y y
               have i₂ := b8e1096
               grind)
            | exact superpose b8e1096 b8e13
            | exact resolve b8e13 b8e1096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1096
          have b8e1765 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1194 (σ x)
               grind)
            | exact superpose b8e1194 b8e20
            | exact resolve b8e20 b8e1194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1194
          have b8e1772 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e1765
               have i₂ := b8e32 x
               grind)
            | exact superpose b8e32 b8e1765
            | exact resolve b8e1765 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e1765
          have b8e1794 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e1772
               have i₂ := b8e1198 x
               grind)
            | exact superpose b8e1198 b8e1772
            | exact resolve b8e1772 b8e1198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1198 b8e1772
          have b8e1795 : False := by grind
          exact b8e1795

/-- `Equation3318`: `x ◇ y = x ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation3318 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3318 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3318.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e28
      have b0e69 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e73 : False := by grind
      exact b0e73
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : False := by grind
        exact b1e28
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : False := by grind
        exact b2e28
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
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
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X0))) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e33 : y = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op X0 X0) X0
               have i₂ := b4e13 X0 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b4e13 y x
               have i₂ := b4e33
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e48 X0 X1
               have i₂ := b4e31 X1
               grind)
            | exact superpose b4e31 b4e48
            | (have j0 := b4e48 X0 X1
               grind)
            | exact resolve b4e48 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e58 : (M.op y x) = (k y (M.op y x)) ∨ y = (M.op y x) := by grind
          have b4e124 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e36 (σ X0)
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e36
            | exact resolve b4e36 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e126 : (M.op (M.op y x) y) = (M.op (M.op y x) (M.op y x)) := by
            first
            | (have i₁ := b4e36 y
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e36
            | exact resolve b4e36 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e131 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e124 X0
               have i₂ := b4e31 (M.op X0 X0)
               grind)
            | exact superpose b4e31 b4e124
            | exact resolve b4e124 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e133 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b4e131 X0
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e131
            | exact resolve b4e131 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e131
          have b4e175 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e342 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e55 x y
               grind)
            | exact superpose b4e55 b4e20
            | (have j1 := b4e55 x y
               grind)
            | exact resolve b4e20 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e386 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e342
               have r₂ := b4e23
               grind)
            | exact resolve b4e342 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342
          have b4e408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e386
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e386
            | exact resolve b4e386 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e386
          have b4e497 : (σ (M.op (M.op y x) y)) = (M.op (σ (M.op y x)) (σ y)) := by
            first
            | (have i₁ := b4e133 y
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e133
            | exact resolve b4e133 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133
          have b4e1018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y x)) ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e408
               have i₂ := b4e54 x y
               grind)
            | exact superpose b4e54 b4e408
            | (have j1 := b4e54 x y
               grind)
            | (have r₁ := b4e408
               have r₂ := b4e54 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e408
               have r₂ := b4e54 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e408 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e1022 : (σ x) = (σ (M.op y x)) ∨ x = y ∨ x = (k y x) := by grind
          clear b4e1018
          have b4e1026 : (σ x) = (σ (M.op y x)) ∨ x = (k y x) := by
            first
            | (have r₁ := b4e1022
               have r₂ := b4e21
               grind)
            | exact resolve b4e1022 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1022
          have b4e1032 : (M.op y x) = (τ (σ x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e14 (M.op y x)
               have i₂ := b4e1026
               grind)
            | exact superpose b4e1026 b4e14
            | exact resolve b4e14 b4e1026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1026
          have b4e1067 : x = (k y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b4e1032
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e1032
            | exact resolve b4e1032 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1032
          have b4e1159 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y x) := by
            first
            | (have i₁ := b4e18 y x
               have i₂ := b4e1067
               grind)
            | exact superpose b4e1067 b4e18
            | (have j0 := b4e18 y x
               grind)
            | exact resolve b4e18 b4e1067
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1067
          have b4e1160 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b4e1159
               have r₂ := b4e21
               grind)
            | exact resolve b4e1159 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1159
          have b4e1168 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b4e1160
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e1160
            | exact resolve b4e1160 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e1160
          have b4e1169 : x = (M.op y x) ∨ x = (M.op x y) := by grind
          clear b4e1168
          have b4e1192 : x = (k y x) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e58
               have i₂ := b4e1169
               grind)
            | exact superpose b4e1169 b4e58
            | exact resolve b4e58 b4e1169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e1195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e497
               have i₂ := b4e1169
               grind)
            | exact superpose b4e1169 b4e497
            | exact resolve b4e497 b4e1169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e497 b4e1169
          have b4e1203 : x = (M.op x y) := by
            first
            | (have r₁ := b4e1195
               have r₂ := b4e20
               grind)
            | exact resolve b4e1195 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1195
          have b4e1205 : x = (k y x) ∨ x = y := by
            first
            | (have j1 := b4e175 x (k y x)
               grind)
            | (have r₁ := b4e1192
               have r₂ := b4e175 y x
               grind)
            | exact resolve b4e1192 b4e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175 b4e1192
          have b4e1207 : x = (k y x) := by
            first
            | (have r₁ := b4e1205
               have r₂ := b4e21
               grind)
            | exact resolve b4e1205 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1205
          have b4e1304 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e408
               have i₂ := b4e1207
               grind)
            | exact superpose b4e1207 b4e408
            | exact resolve b4e408 b4e1207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e408 b4e1207
          have b4e1309 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e1304
               have i₂ := b4e1203
               grind)
            | exact superpose b4e1203 b4e1304
            | exact resolve b4e1304 b4e1203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1304
          have b4e1310 : (σ x) = (σ (M.op y x)) := by grind
          clear b4e1309
          have b4e1411 : (M.op y x) = (τ (σ x)) := by
            first
            | (have i₁ := b4e14 (M.op y x)
               have i₂ := b4e1310
               grind)
            | exact superpose b4e1310 b4e14
            | exact resolve b4e14 b4e1310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1414 : (M.op (σ x) (σ x)) = (σ (M.op (M.op y x) (M.op y x))) := by
            first
            | (have i₁ := b4e31 (M.op y x)
               have i₂ := b4e1310
               grind)
            | exact superpose b4e1310 b4e31
            | exact resolve b4e31 b4e1310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e1310
          have b4e1445 : (M.op (σ x) (σ x)) = (σ (M.op (M.op y x) y)) := by
            first
            | (have i₁ := b4e1414
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e1414
            | exact resolve b4e1414 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126 b4e1414
          have b4e1448 : x = (M.op y x) := by
            first
            | (have i₁ := b4e1411
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e1411
            | exact resolve b4e1411 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1411
          have b4e1453 : (σ y) = (σ (M.op (M.op y x) y)) := by
            first
            | (have i₁ := b4e1445
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1445
            | exact resolve b4e1445 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1445
          have b4e1457 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b4e1453
               have i₂ := b4e1448
               grind)
            | exact superpose b4e1448 b4e1453
            | exact resolve b4e1453 b4e1448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1448 b4e1453
          have b4e1460 : (σ x) = (σ y) := by
            first
            | (have i₁ := b4e1457
               have i₂ := b4e1203
               grind)
            | exact superpose b4e1203 b4e1457
            | exact resolve b4e1457 b4e1203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1203 b4e1457
          have b4e1462 : False := by grind
          exact b4e1462
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e79 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e24
            | exact resolve b5e24 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e84 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e79
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e79
            | exact resolve b5e79 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e85 : False := by grind
          exact b5e85
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : x = y := by
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
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e94 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e24
            | exact resolve b7e24 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e114 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e14
            | exact resolve b7e14 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e115 : y = (M.op x x) := by
            first
            | (have i₁ := b7e114
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e114
            | exact resolve b7e114 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e119 : False := by grind
          exact b7e119
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X0))) := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e34 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e13 (M.op X0 X0) X0
               have i₂ := b8e13 X0 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e31 X1
               grind)
            | exact superpose b8e31 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e77 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e34 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e34
            | exact resolve b8e34 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e77 X0
               have i₂ := b8e31 (M.op X0 X0)
               grind)
            | exact superpose b8e31 b8e77
            | exact resolve b8e77 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e77
          have b8e84 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b8e83 X0
               have i₂ := b8e34 X0
               grind)
            | exact superpose b8e34 b8e83
            | exact resolve b8e83 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e83
          have b8e241 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e20
            | (have j1 := b8e65 x y
               grind)
            | exact resolve b8e20 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e284 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e241
               have r₂ := b8e23
               grind)
            | exact resolve b8e241 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e241
          have b8e771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e284
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e284
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e284
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e284
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e284 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e284
          have b8e773 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b8e771
          have b8e777 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b8e773
               have r₂ := b8e21
               grind)
            | exact resolve b8e773 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e773
          have b8e784 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e777
               grind)
            | exact superpose b8e777 b8e14
            | exact resolve b8e14 b8e777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e777
          have b8e819 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e784
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e784
            | exact resolve b8e784 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e784
          have b8e820 : x = (M.op y y) := by grind
          clear b8e819
          have b8e880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e84 y
               have i₂ := b8e820
               grind)
            | exact superpose b8e820 b8e84
            | exact resolve b8e84 b8e820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84 b8e820
          have b8e884 : False := by grind
          exact b8e884
