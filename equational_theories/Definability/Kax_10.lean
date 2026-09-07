import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3479`: `x ◇ x = y ◇ ((x ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3479 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3479 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3479.models_iff G M).mp hM
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
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e21
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e23 : False := by grind
      exact b0e23
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y ≠ y ∨ x = (k x y) := by
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
        have b1e28 : x = (k x y) := by grind
        clear b1e26
        have b1e66 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e71 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e66
        have b1e72 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e71
             have r₂ := b1e23
             grind)
          | exact resolve b1e71 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e73 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e72
          | exact resolve b1e72 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e74 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e73
          | exact resolve b1e73 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e73
        have b1e75 : False := by grind
        exact b1e75
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y ≠ y ∨ x = (k x y) := by
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
        have b2e25 : x = (k x y) := by grind
        clear b2e24
        have b2e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e572 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e95 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e18930 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e572 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e572
          | (have j0 := b2e572 x y
             grind)
          | exact resolve b2e572 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e572
        have b2e18939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e18930
        have b2e18966 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e18939
             have r₂ := b2e22
             grind)
          | exact resolve b2e18939 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18939
        have b2e18977 : False := by grind
        exact b2e18977
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e24
          | exact resolve b3e24 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e28
          | exact resolve b3e28 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e50 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e53 : x = y ∨ y = (k x y) := by grind
        clear b3e50
        have b3e54 : y = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e23
             grind)
          | exact resolve b3e53 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e53
        have b3e57 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e29
          | exact resolve b3e29 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e54
        have b3e58 : False := by grind
        exact b3e58
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e27
            | exact resolve b4e27 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e29 : False := by grind
          exact b4e29
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e58 : x = y ∨ y = (k x y) := by grind
          clear b5e53
          have b5e59 : y = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e25
               grind)
            | exact resolve b5e58 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e58
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e954 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e8069 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e954 x y
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e954
            | (have j0 := b5e954 x y
               grind)
            | exact resolve b5e954 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e954
          have b5e8076 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e8069
          have b5e8079 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e8076
               have r₂ := b5e24
               grind)
            | exact resolve b5e8076 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8076
          have b5e8088 : False := by grind
          exact b5e8088
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e24
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
        have b6e31 : (k x y) = (τ (σ x)) := by
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
        have b6e32 : x = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e71 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e73 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e71
        have b6e76 : y = (M.op x y) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e21
             grind)
          | exact resolve b6e73 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e79 : False := by grind
        exact b6e79
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e65 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e60
          have b7e66 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e25
               grind)
            | exact resolve b7e65 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e65
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
          have b7e70 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e71 : y = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e80 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e81 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e80
          have b7e83 : x = (M.op x y) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e21
               grind)
            | exact resolve b7e81 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e85 : False := by grind
          exact b7e85
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e559 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e88 x y
               grind)
            | exact superpose b8e88 b8e20
            | (have j1 := b8e88 x y
               grind)
            | exact resolve b8e20 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e601 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e559
               have r₂ := b8e24
               grind)
            | exact resolve b8e559 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e559
          have b8e604 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e601
               have r₂ := b8e23
               grind)
            | exact resolve b8e601 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e601
          have b8e676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e604
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e604
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e604 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e604
          have b8e677 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e676
          have b8e678 : y = (M.op x y) := by
            first
            | (have r₁ := b8e677
               have r₂ := b8e22
               grind)
            | exact resolve b8e677 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e677
          have b8e679 : False := by grind
          exact b8e679

/-- `Equation3481`: `x ◇ x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxx_x_pxy_Equation3481 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e21
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e40 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e42
      have b0e45 : (M.op x x) = (k x y) := by grind
      clear b0e40
      have b0e46 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e44
        | exact resolve b0e44 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e47 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e46
        | exact resolve b0e46 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e46
      have b0e48 : False := by grind
      exact b0e48
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : (M.op y y) = (M.op x (M.op (M.op x x) y)) := by
          first
          | (have i₁ := b1e12 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e52
        have b1e55 : (M.op x x) = (k x y) := by grind
        clear b1e50
        have b1e56 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e57 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e53 y
             grind)
          | exact superpose b1e53 b1e56
          | exact resolve b1e56 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e53 (σ X0)
             grind)
          | exact superpose b1e53 b1e18
          | exact resolve b1e18 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e59 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e59
          | exact resolve b1e59 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e59
        have b1e72 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e72 X0
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e72
          | (have j0 := b1e72 X0
             grind)
          | exact resolve b1e72 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e125 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e23
          | exact resolve b1e23 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e763 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e74 (σ x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e74
          | (have j0 := b1e74 (σ x)
             grind)
          | (have r₁ := b1e74 (σ x)
             have r₂ := b1e57
             grind)
          | exact resolve b1e74 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e74
        have b1e764 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e763
        have b1e765 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e764
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e764
          | exact resolve b1e764 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e764
        have b1e767 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e765
             have r₂ := b1e125
             grind)
          | exact resolve b1e765 b1e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e765
        have b1e768 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e767
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e767
          | exact resolve b1e767 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e767
        have b1e769 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e768
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e768
          | exact resolve b1e768 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e768
        have b1e771 : (M.op x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e769
             grind)
          | exact superpose b1e769 b1e13
          | exact resolve b1e13 b1e769
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e783 : x = (M.op x x) := by
          first
          | (have i₁ := b1e771
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e771
          | exact resolve b1e771 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e771
        have b1e852 : (M.op y y) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e783
             grind)
          | exact superpose b1e783 b1e26
          | exact resolve b1e26 b1e783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e876 : (M.op y y) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b1e852
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e852
          | exact resolve b1e852 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e852
        have b1e881 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e876
             have i₂ := b1e783
             grind)
          | exact superpose b1e783 b1e876
          | exact resolve b1e876 b1e783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e876
        have b1e884 : x = (M.op y y) := by
          first
          | (have i₁ := b1e881
             have i₂ := b1e783
             grind)
          | exact superpose b1e783 b1e881
          | exact resolve b1e881 b1e783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e783 b1e881
        have b1e960 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e125
             have i₂ := b1e884
             grind)
          | exact superpose b1e884 b1e125
          | exact resolve b1e125 b1e884
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125 b1e884
        have b1e984 : False := by grind
        exact b1e984
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op x x) = (k x y) := by grind
        clear b2e48
        have b2e87 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ y) (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1231 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e1232 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1231
             have r₂ := b2e21
             grind)
          | exact resolve b2e1231 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1231
        have b2e1233 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1232
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1232
          | exact resolve b2e1232 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1232
        have b2e1234 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1233
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e1233
          | exact resolve b2e1233 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e1233
        have b2e1235 : False := by grind
        exact b2e1235
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) (M.op (M.op X1 X0) X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op (M.op X1 X0) X0) X1
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e12 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e52
        have b3e56 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e53 (σ X0)
             grind)
          | exact superpose b3e53 b3e18
          | exact resolve b3e18 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e59 X0
             have i₂ := b3e53 X0
             grind)
          | exact superpose b3e53 b3e59
          | exact resolve b3e59 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e72 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e74 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e23
          | exact resolve b3e23 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e77 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e15
          | exact resolve b3e15 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e79 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e77
        have b3e80 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e79
          | exact resolve b3e79 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e81 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e53 x
             grind)
          | exact superpose b3e53 b3e80
          | exact resolve b3e80 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e103 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X1) X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e12 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X1
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e142 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e13
          | exact resolve b3e13 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e143 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b3e142
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e142
          | exact resolve b3e142 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e142
        have b3e211 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
          first
          | (have j0 := b3e72 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e212 : x = (k x y) := by
          first
          | (have r₁ := b3e211
             have r₂ := b3e20
             grind)
          | exact resolve b3e211 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e211
        have b3e215 : x = (M.op x x) := by
          first
          | (have i₁ := b3e143
             have i₂ := b3e212
             grind)
          | exact superpose b3e212 b3e143
          | exact resolve b3e143 b3e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e216 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e212
             grind)
          | exact superpose b3e212 b3e81
          | exact resolve b3e81 b3e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e217 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e74
             have i₂ := b3e212
             grind)
          | exact superpose b3e212 b3e74
          | exact resolve b3e74 b3e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74 b3e212
        have b3e523 : (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y)))) := by
          first
          | (have i₁ := b3e31 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e31
          | exact resolve b3e31 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e559 : (M.op (M.op (σ (k x y)) (σ y)) (M.op (σ (k x y)) (σ y))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ (k x y)) (σ y)))) := by
          first
          | (have i₁ := b3e523
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e523
          | exact resolve b3e523 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e523
        have b3e569 : (M.op (M.op (σ (M.op x x)) (σ y)) (M.op (σ (M.op x x)) (σ y))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ (M.op x x)) (σ y)))) := by
          first
          | (have i₁ := b3e559
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e559
          | exact resolve b3e559 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e559
        have b3e571 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y)))) := by
          first
          | (have i₁ := b3e569
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e569
          | exact resolve b3e569 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e569
        have b3e573 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b3e571
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e571
          | exact resolve b3e571 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e571
        have b3e575 : (M.op (σ (k x y)) (σ (k x y))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (σ (k x y)))) := by
          first
          | (have i₁ := b3e573
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e573
          | exact resolve b3e573 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e573
        have b3e577 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (σ (M.op x x)))) := by
          first
          | (have i₁ := b3e575
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e575
          | exact resolve b3e575 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e575
        have b3e579 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (σ x))) := by
          first
          | (have i₁ := b3e577
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e577
          | exact resolve b3e577 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e577
        have b3e581 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op y y)) (σ x))) := by
          first
          | (have i₁ := b3e579
             have i₂ := b3e66 y
             grind)
          | exact superpose b3e66 b3e579
          | exact resolve b3e579 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e579
        have b3e583 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b3e581
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e581
          | exact resolve b3e581 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e581
        have b3e585 : (σ (k x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b3e583
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e583
          | exact resolve b3e583 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e583
        have b3e587 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b3e585
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e585
          | exact resolve b3e585 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e585
        have b3e589 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b3e587
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e587
          | exact resolve b3e587 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e587
        have b3e924 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e103 (σ x) (M.op (M.op (σ x) (σ x)) (σ y))
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e103
          | exact resolve b3e103 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e103
        have b3e996 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (k x y)) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ (k x y)) (σ y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e924
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e924
          | exact resolve b3e924 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e924
        have b3e999 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x x)) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ (M.op x x)) (σ y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e996
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e996
          | exact resolve b3e996 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e996
        have b3e1000 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e999
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e999
          | exact resolve b3e999 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e999
        have b3e1001 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ x)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1000
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1000
          | exact resolve b3e1000 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1000
        have b3e1002 : (M.op (σ y) (σ y)) = (M.op (σ (k x y)) (M.op (M.op (σ y) (σ y)) (σ (k x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1001
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e1001
          | exact resolve b3e1001 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1001
        have b3e1003 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (M.op (M.op (σ y) (σ y)) (σ (M.op x x)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1002
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e1002
          | exact resolve b3e1002 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1002
        have b3e1004 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (σ y)) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1003
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e1003
          | exact resolve b3e1003 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1003
        have b3e1005 : (σ (M.op y y)) = (M.op (σ x) (M.op (σ (M.op y y)) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1004
             have i₂ := b3e66 y
             grind)
          | exact superpose b3e66 b3e1004
          | exact resolve b3e1004 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1004
        have b3e1006 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1005
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1005
          | exact resolve b3e1005 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1005
        have b3e1007 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1006
             have i₂ := b3e589
             grind)
          | exact superpose b3e589 b3e1006
          | exact resolve b3e1006 b3e589
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e589 b3e1006
        have b3e1008 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have r₁ := b3e1007
             have r₂ := b3e217
             grind)
          | exact resolve b3e1007 b3e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1007
        have b3e1009 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1008
             have i₂ := b3e66 y
             grind)
          | exact superpose b3e66 b3e1008
          | exact resolve b3e1008 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1008
        have b3e1010 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have i₁ := b3e1009
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1009
          | exact resolve b3e1009 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1009
        have b3e1011 : (M.op (σ y) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) := by
          first
          | (have r₁ := b3e1010
             have r₂ := b3e23
             grind)
          | exact resolve b3e1010 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1010
        have b3e1012 : (M.op (σ y) (σ y)) = (k (σ x) (M.op (σ (k x y)) (σ y))) := by
          first
          | (have i₁ := b3e1011
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e1011
          | exact resolve b3e1011 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1011
        have b3e1013 : (M.op (σ y) (σ y)) = (k (σ x) (M.op (σ (M.op x x)) (σ y))) := by
          first
          | (have i₁ := b3e1012
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e1012
          | exact resolve b3e1012 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e1012
        have b3e1014 : (M.op (σ y) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b3e1013
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e1013
          | exact resolve b3e1013 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1013
        have b3e1015 : (M.op (σ y) (σ y)) = (k (σ x) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e1014
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1014
          | exact resolve b3e1014 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1014
        have b3e1016 : (M.op (σ y) (σ y)) = (k (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b3e1015
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e1015
          | exact resolve b3e1015 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e1015
        have b3e1017 : (M.op (σ y) (σ y)) = (σ (k x (k x y))) := by
          first
          | (have i₁ := b3e1016
             have i₂ := b3e18 x (k x y)
             grind)
          | exact superpose b3e18 b3e1016
          | exact resolve b3e1016 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1016
        have b3e1018 : (M.op (σ y) (σ y)) = (σ (k x (M.op x x))) := by
          first
          | (have i₁ := b3e1017
             have i₂ := b3e143
             grind)
          | exact superpose b3e143 b3e1017
          | exact resolve b3e1017 b3e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e143 b3e1017
        have b3e1019 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e1018
             have i₂ := b3e215
             grind)
          | exact superpose b3e215 b3e1018
          | exact resolve b3e1018 b3e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215 b3e1018
        have b3e1020 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e1019
             have i₂ := b3e53 x
             grind)
          | exact superpose b3e53 b3e1019
          | exact resolve b3e1019 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e1019
        have b3e1021 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1020
             have i₂ := b3e216
             grind)
          | exact superpose b3e216 b3e1020
          | exact resolve b3e1020 b3e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e216 b3e1020
        have b3e1022 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1021
             have i₂ := b3e66 y
             grind)
          | exact superpose b3e66 b3e1021
          | exact resolve b3e1021 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66 b3e1021
        have b3e1023 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b3e1022
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1022
          | exact resolve b3e1022 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1022
        have b3e1024 : False := by grind
        exact b3e1024
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e66
          have b4e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e68
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e68
            | exact resolve b4e68 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e72 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e67 y
               grind)
            | exact superpose b4e67 b4e70
            | exact resolve b4e70 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e70
          have b4e73 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e72
            | exact resolve b4e72 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e74 : False := by grind
          exact b4e74
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e64 (σ X0)
               grind)
            | exact superpose b5e64 b5e19
            | exact resolve b5e19 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e68 X0
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e68
            | exact resolve b5e68 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e68
          have b5e85 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e120 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e220 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e221 : x = (k x y) := by
            first
            | (have r₁ := b5e220
               have r₂ := b5e21
               grind)
            | exact resolve b5e220 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220
          have b5e1351 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1352 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1351
               have r₂ := b5e23
               grind)
            | exact resolve b5e1351 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1351
          have b5e1353 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1352
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1352
            | exact resolve b5e1352 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1352
          have b5e1354 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1353
               have i₂ := b5e221
               grind)
            | exact superpose b5e221 b5e1353
            | exact resolve b5e1353 b5e221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e221 b5e1353
          have b5e1360 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b5e13 (σ y) (σ x)
               have i₂ := b5e1354
               grind)
            | exact superpose b5e1354 b5e13
            | exact resolve b5e13 b5e1354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1370 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1360
               have i₂ := b5e1354
               grind)
            | exact superpose b5e1354 b5e1360
            | exact resolve b5e1360 b5e1354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1354 b5e1360
          have b5e1377 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1370
               have i₂ := b5e77 y
               grind)
            | exact superpose b5e77 b5e1370
            | exact resolve b5e1370 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1370
          have b5e1382 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1377
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1377
            | exact resolve b5e1377 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1377
          have b5e1387 : (σ (M.op x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1382
               have i₂ := b5e77 x
               grind)
            | exact superpose b5e77 b5e1382
            | exact resolve b5e1382 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e1382
          have b5e1914 : (M.op x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b5e14 (M.op x y)
               have i₂ := b5e1387
               grind)
            | exact superpose b5e1387 b5e14
            | exact resolve b5e14 b5e1387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1387
          have b5e1950 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b5e1914
               have i₂ := b5e14 (M.op x x)
               grind)
            | exact superpose b5e14 b5e1914
            | exact resolve b5e1914 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1914
          have b5e1951 : False := by grind
          exact b5e1951
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e51
          | exact resolve b6e51 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e68 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e23
          | exact resolve b6e23 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e52
        have b6e123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e68
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e68
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e68 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e124 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e123
        have b6e125 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e124
             have r₂ := b6e20
             grind)
          | exact resolve b6e124 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e126 : False := by grind
        exact b6e126
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e63 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e63
          have b7e66 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e64 y
               grind)
            | exact superpose b7e64 b7e66
            | exact resolve b7e66 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e64 (σ X0)
               grind)
            | exact superpose b7e64 b7e19
            | exact resolve b7e19 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e69 X0
               have i₂ := b7e64 X0
               grind)
            | exact superpose b7e64 b7e69
            | exact resolve b7e69 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e69
          have b7e86 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e17 X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 X0 (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e88 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e86 X0
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e86
            | (have j0 := b7e86 X0
               grind)
            | exact resolve b7e86 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e89 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e23
            | exact resolve b7e23 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e89
            | exact resolve b7e89 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e16 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X0 X0
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e129 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e110 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e445 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e129 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e129
          have b7e455 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e445 X0 X1
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e445 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e445 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e445 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e445 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e445
          have b7e746 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e88 (σ x)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e88
            | (have j0 := b7e88 (σ x)
               grind)
            | (have r₁ := b7e88 (σ x)
               have r₂ := b7e67
               grind)
            | exact resolve b7e88 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e88
          have b7e747 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e746
          have b7e748 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e747
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e747
            | exact resolve b7e747 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e747
          have b7e750 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e748
               have r₂ := b7e95
               grind)
            | exact resolve b7e748 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e748
          have b7e751 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e750
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e750
            | exact resolve b7e750 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e750
          have b7e756 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e751
               grind)
            | exact superpose b7e751 b7e14
            | exact resolve b7e14 b7e751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e751
          have b7e768 : x = (k x y) := by
            first
            | (have i₁ := b7e756
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e756
            | exact resolve b7e756 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e756
          have b7e840 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e455 x y
               have i₂ := b7e768
               grind)
            | exact superpose b7e768 b7e455
            | (have j0 := b7e455 x y
               grind)
            | exact resolve b7e455 b7e768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e455 b7e768
          have b7e847 : x = (M.op x y) := by
            first
            | (have r₁ := b7e840
               have r₂ := b7e22
               grind)
            | exact resolve b7e840 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e840
          have b7e926 : (M.op y y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e13 y x
               have i₂ := b7e847
               grind)
            | exact superpose b7e847 b7e13
            | exact resolve b7e13 b7e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e932 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e926
               have i₂ := b7e847
               grind)
            | exact superpose b7e847 b7e926
            | exact resolve b7e926 b7e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e847 b7e926
          have b7e1254 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e932
               grind)
            | exact superpose b7e932 b7e95
            | exact resolve b7e95 b7e932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95 b7e932
          have b7e1276 : False := by grind
          exact b7e1276
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e113 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e124 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e104 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e347 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e124 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e357 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e347 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e347 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e347 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e347 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e347 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e347
          have b8e1266 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e113 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e1267 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1266
               have r₂ := b8e23
               grind)
            | exact resolve b8e1266 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1266
          have b8e1268 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1267
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1267
            | exact resolve b8e1267 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1267
          have b8e1273 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1268
               grind)
            | exact superpose b8e1268 b8e20
            | exact resolve b8e20 b8e1268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1268
          have b8e1327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1273
               have i₂ := b8e357 x y
               grind)
            | exact superpose b8e357 b8e1273
            | (have j1 := b8e357 x y
               grind)
            | exact resolve b8e1273 b8e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e357 b8e1273
          have b8e1334 : (M.op x y) = (M.op y y) := by grind
          clear b8e1327
          have b8e1338 : False := by grind
          exact b8e1338

/-- `Equation3481`: `x ◇ x = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_x_pxy_Equation3481 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e21
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e43 (σ X0)
           grind)
        | exact superpose b0e43 b0e17
        | exact resolve b0e17 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e50 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e50
        | exact resolve b0e50 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e50
      have b0e199 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e55 x
           grind)
        | exact superpose b0e55 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e55 x
           grind)
        | exact resolve b0e22 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e55
      have b0e208 : False := by grind
      exact b0e208
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e52
        have b1e55 : (M.op y y) = (k x y) := by grind
        clear b1e50
        have b1e56 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e58 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e53 y
             grind)
          | exact superpose b1e53 b1e56
          | exact resolve b1e56 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e53 (σ X0)
             grind)
          | exact superpose b1e53 b1e18
          | exact resolve b1e18 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e60 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e60
          | exact resolve b1e60 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e60
        have b1e73 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e73 X0
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e73
          | (have j0 := b1e73 X0
             grind)
          | exact resolve b1e73 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e125 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e23
          | exact resolve b1e23 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e127 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op y y)) (σ y))) := by
          first
          | (have i₁ := b1e12 (σ y) (σ x)
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e12
          | exact resolve b1e12 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e128 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op y y)) (σ y))) := by
          first
          | (have i₁ := b1e127
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e127
          | exact resolve b1e127 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127
        have b1e131 : (σ (M.op y y)) = (M.op (σ x) (M.op (σ (M.op y y)) (σ y))) := by
          first
          | (have i₁ := b1e128
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e128
          | exact resolve b1e128 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e128
        have b1e573 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e75 (σ x)
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e75
          | (have j0 := b1e75 (σ x)
             grind)
          | (have r₁ := b1e75 (σ x)
             have r₂ := b1e58
             grind)
          | exact resolve b1e75 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e574 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e573
        have b1e575 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e574
             have i₂ := b1e67 x
             grind)
          | exact superpose b1e67 b1e574
          | exact resolve b1e574 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e574
        have b1e577 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e575
             have r₂ := b1e125
             grind)
          | exact resolve b1e575 b1e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e575
        have b1e578 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e577
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e577
          | exact resolve b1e577 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e577
        have b1e579 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e578
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e578
          | exact resolve b1e578 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e578
        have b1e581 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e125
             have i₂ := b1e579
             grind)
          | exact superpose b1e579 b1e125
          | exact resolve b1e125 b1e579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125
        have b1e3166 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b1e131
             have i₂ := b1e579
             grind)
          | exact superpose b1e579 b1e131
          | exact resolve b1e131 b1e579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e3205 : (σ x) = (M.op (σ x) (σ (M.op y y))) := by
          first
          | (have i₁ := b1e3166
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e3166
          | exact resolve b1e3166 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e3166
        have b1e3225 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e3205
             have i₂ := b1e579
             grind)
          | exact superpose b1e579 b1e3205
          | exact resolve b1e3205 b1e579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e579 b1e3205
        have b1e3243 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e3225
             have i₂ := b1e67 x
             grind)
          | exact superpose b1e67 b1e3225
          | exact resolve b1e3225 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e3225
        have b1e3261 : False := by grind
        exact b1e3261
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op y y) = (k x y) := by grind
        clear b2e48
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e50 (σ X0)
             grind)
          | exact superpose b2e50 b2e18
          | exact resolve b2e18 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e50 X0
             grind)
          | exact superpose b2e50 b2e54
          | exact resolve b2e54 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e54
        have b2e88 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ y) (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e136 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e61 y
             grind)
          | exact superpose b2e61 b2e22
          | exact resolve b2e22 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1081 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e88 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88
        have b2e1082 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1081
             have r₂ := b2e21
             grind)
          | exact resolve b2e1081 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1081
        have b2e1083 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1082
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1082
          | exact resolve b2e1082 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1082
        have b2e1084 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1083
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e1083
          | exact resolve b2e1083 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e1083
        have b2e1085 : False := by grind
        exact b2e1085
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e52
        have b3e56 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e73 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e77 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e15
          | exact resolve b3e15 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e79 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e77
        have b3e80 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e79
          | exact resolve b3e79 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e81 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e80
          | exact resolve b3e80 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e80
        have b3e82 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e81
          | exact resolve b3e81 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e132 : (k x y) = (τ (σ (M.op x y))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e82
             grind)
          | exact superpose b3e82 b3e13
          | exact resolve b3e13 b3e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e133 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b3e132
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e132
          | exact resolve b3e132 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132
        have b3e211 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
          first
          | (have j0 := b3e73 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e212 : x = (k x y) := by
          first
          | (have r₁ := b3e211
             have r₂ := b3e20
             grind)
          | exact resolve b3e211 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e211
        have b3e215 : x = (M.op x y) := by
          first
          | (have i₁ := b3e133
             have i₂ := b3e212
             grind)
          | exact superpose b3e212 b3e133
          | exact resolve b3e133 b3e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e133 b3e212
        have b3e264 : (M.op y y) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b3e12 y x
             have i₂ := b3e215
             grind)
          | exact superpose b3e215 b3e12
          | exact resolve b3e12 b3e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e266 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e264
             have i₂ := b3e215
             grind)
          | exact superpose b3e215 b3e264
          | exact resolve b3e264 b3e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215 b3e264
        have b3e476 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e266
             grind)
          | exact superpose b3e266 b3e21
          | exact resolve b3e21 b3e266
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e266
        have b3e489 : False := by grind
        exact b3e489
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e66
          have b4e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e68
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e68
            | exact resolve b4e68 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e73 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e67 y
               grind)
            | exact superpose b4e67 b4e70
            | exact resolve b4e70 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e70
          have b4e74 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e73
            | exact resolve b4e73 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e75 : False := by grind
          exact b4e75
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e64 (σ X0)
               grind)
            | exact superpose b5e64 b5e19
            | exact resolve b5e19 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e69 X0
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e69
            | exact resolve b5e69 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e69
          have b5e86 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e121 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e212 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
            first
            | (have j0 := b5e86 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e213 : x = (k x y) := by
            first
            | (have r₁ := b5e212
               have r₂ := b5e21
               grind)
            | exact resolve b5e212 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e212
          have b5e1266 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e121 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e121
          have b5e1267 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1266
               have r₂ := b5e23
               grind)
            | exact resolve b5e1266 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1266
          have b5e1268 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1267
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1267
            | exact resolve b5e1267 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1267
          have b5e1269 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1268
               have i₂ := b5e213
               grind)
            | exact superpose b5e213 b5e1268
            | exact resolve b5e1268 b5e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213 b5e1268
          have b5e1275 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b5e13 (σ y) (σ x)
               have i₂ := b5e1269
               grind)
            | exact superpose b5e1269 b5e13
            | exact resolve b5e13 b5e1269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1285 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1275
               have i₂ := b5e1269
               grind)
            | exact superpose b5e1269 b5e1275
            | exact resolve b5e1275 b5e1269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1269 b5e1275
          have b5e1292 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1285
               have i₂ := b5e78 y
               grind)
            | exact superpose b5e78 b5e1285
            | exact resolve b5e1285 b5e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1285
          have b5e1297 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1292
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1292
            | exact resolve b5e1292 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1292
          have b5e1302 : (σ (M.op x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1297
               have i₂ := b5e78 x
               grind)
            | exact superpose b5e78 b5e1297
            | exact resolve b5e1297 b5e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78 b5e1297
          have b5e1918 : (M.op x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b5e14 (M.op x y)
               have i₂ := b5e1302
               grind)
            | exact superpose b5e1302 b5e14
            | exact resolve b5e14 b5e1302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1302
          have b5e1960 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b5e1918
               have i₂ := b5e14 (M.op x x)
               grind)
            | exact superpose b5e14 b5e1918
            | exact resolve b5e1918 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1918
          have b5e1961 : False := by grind
          exact b5e1961
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e51
          | exact resolve b6e51 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e71 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e15
          | exact resolve b6e15 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e73 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e71
        have b6e74 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e73
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e73
          | exact resolve b6e73 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e75 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e74
             have i₂ := b6e50 y
             grind)
          | exact superpose b6e50 b6e74
          | exact resolve b6e74 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50 b6e74
        have b6e126 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e75
             grind)
          | exact superpose b6e75 b6e13
          | exact resolve b6e13 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e127 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e126
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e126
          | exact resolve b6e126 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126
        have b6e151 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e127
             grind)
          | exact superpose b6e127 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127
        have b6e152 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e151
        have b6e154 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e152
             have r₂ := b6e21
             grind)
          | exact resolve b6e152 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e152
        have b6e156 : False := by grind
        exact b6e156
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e63 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e63
          have b7e66 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e64 y
               grind)
            | exact superpose b7e64 b7e66
            | exact resolve b7e66 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e64 (σ X0)
               grind)
            | exact superpose b7e64 b7e19
            | exact resolve b7e19 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e70 X0
               have i₂ := b7e64 X0
               grind)
            | exact superpose b7e64 b7e70
            | exact resolve b7e70 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e70
          have b7e87 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e17 X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 X0 (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e89 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e87 X0
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e87
            | (have j0 := b7e87 X0
               grind)
            | exact resolve b7e87 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e23
            | exact resolve b7e23 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e90
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e90
            | exact resolve b7e90 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e559 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e89 (σ x)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e89
            | (have j0 := b7e89 (σ x)
               grind)
            | (have r₁ := b7e89 (σ x)
               have r₂ := b7e68
               grind)
            | exact resolve b7e89 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e89
          have b7e560 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e559
          have b7e561 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e560
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e560
            | exact resolve b7e560 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e560
          have b7e563 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e561
               have r₂ := b7e96
               grind)
            | exact resolve b7e561 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e561
          have b7e564 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e563
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e563
            | exact resolve b7e563 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e563
          have b7e568 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e564
               grind)
            | exact superpose b7e564 b7e14
            | exact resolve b7e14 b7e564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e564
          have b7e587 : x = (k x y) := by
            first
            | (have i₁ := b7e568
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e568
            | exact resolve b7e568 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e568
          have b7e650 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e587
               grind)
            | exact superpose b7e587 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e587
          have b7e651 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e650
               have r₂ := b7e21
               grind)
            | exact resolve b7e650 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e650
          have b7e657 : x = (M.op x y) := by
            first
            | (have r₁ := b7e651
               have r₂ := b7e22
               grind)
            | exact resolve b7e651 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e651
          have b7e725 : (M.op y y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b7e13 y x
               have i₂ := b7e657
               grind)
            | exact superpose b7e657 b7e13
            | exact resolve b7e13 b7e657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e731 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e725
               have i₂ := b7e657
               grind)
            | exact superpose b7e657 b7e725
            | exact resolve b7e725 b7e657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e657 b7e725
          have b7e978 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e96
               have i₂ := b7e731
               grind)
            | exact superpose b7e731 b7e96
            | exact resolve b7e96 b7e731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96 b7e731
          have b7e995 : False := by grind
          exact b7e995
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e114 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1126 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e114 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e1127 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1126
               have r₂ := b8e23
               grind)
            | exact resolve b8e1126 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1126
          have b8e1128 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1127
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1127
            | exact resolve b8e1127 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1127
          have b8e1133 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1128
               grind)
            | exact superpose b8e1128 b8e20
            | exact resolve b8e20 b8e1128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1128
          have b8e1215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1133
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1133
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1133 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1133
          have b8e1216 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1215
          have b8e1218 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1216
               have r₂ := b8e21
               grind)
            | exact resolve b8e1216 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1216
          have b8e1221 : False := by grind
          exact b8e1221

/-- `Equation3493`: `x ◇ x = y ◇ ((z ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3493 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3493 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3493.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e21
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e23 : False := by grind
      exact b0e23
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : x ≠ x ∨ y = (k x y) := by
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
        have b1e28 : y = (k x y) := by grind
        clear b1e26
        have b1e65 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e70 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e65
        have b1e72 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e70
             have r₂ := b1e23
             grind)
          | exact resolve b1e70 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e73 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e72
          | exact resolve b1e72 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e74 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e73
          | exact resolve b1e73 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e73
        have b1e75 : False := by grind
        exact b1e75
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x ≠ x ∨ y = (k x y) := by
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
        have b2e25 : y = (k x y) := by grind
        clear b2e24
        have b2e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1049 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e96 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e21859 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1049 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1049
          | (have j0 := b2e1049 x y
             grind)
          | exact resolve b2e1049 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1049
        have b2e21868 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e21859
        have b2e21878 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e21868
             have r₂ := b2e22
             grind)
          | exact resolve b2e21868 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21868
        have b2e21882 : False := by grind
        exact b2e21882
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e24
          | exact resolve b3e24 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e28
          | exact resolve b3e28 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e49 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e52 : x = y ∨ x = (k x y) := by grind
        clear b3e49
        have b3e53 : x = (k x y) := by
          first
          | (have r₁ := b3e52
             have r₂ := b3e23
             grind)
          | exact resolve b3e52 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e52
        have b3e56 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e29
          | exact resolve b3e29 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e53
        have b3e57 : False := by grind
        exact b3e57
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e27
            | exact resolve b4e27 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e29 : False := by grind
          exact b4e29
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e52 : x = y ∨ x = (k x y) := by grind
          clear b5e48
          have b5e53 : x = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e25
               grind)
            | exact resolve b5e52 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e52
          have b5e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e1105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e23299 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1105 x y
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e1105
            | (have j0 := b5e1105 x y
               grind)
            | exact resolve b5e1105 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e1105
          have b5e23308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e23299
          have b5e23320 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e23308
               have r₂ := b5e24
               grind)
            | exact resolve b5e23308 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23308
          have b5e23324 : False := by grind
          exact b5e23324
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e24
        have b6e26 : (σ y) = (σ (k x y)) := by
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
        have b6e31 : (k x y) = (τ (σ y)) := by
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
        have b6e32 : y = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e71 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e73 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e71
        have b6e76 : x = (M.op x y) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e21
             grind)
          | exact resolve b6e73 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e79 : False := by grind
        exact b6e79
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e64 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e59
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e67 : (σ x) = (σ (k x y)) := by
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
          have b7e70 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e71 : x = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e80 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e81 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e80
          have b7e83 : y = (M.op x y) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e21
               grind)
            | exact resolve b7e81 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e85 : False := by grind
          exact b7e85
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1200 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e89 x y
               grind)
            | exact superpose b8e89 b8e20
            | (have j1 := b8e89 x y
               grind)
            | exact resolve b8e20 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e1259 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1200
               have r₂ := b8e24
               grind)
            | exact resolve b8e1200 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1200
          have b8e1263 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1259
               have r₂ := b8e23
               grind)
            | exact resolve b8e1259 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1259
          have b8e1265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1263
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1263
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1263 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1263
          have b8e1266 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e1265
          have b8e1267 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1266
               have r₂ := b8e22
               grind)
            | exact resolve b8e1266 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1266
          have b8e1268 : False := by grind
          exact b8e1268

/-- `Equation3493`: `x ◇ x = y ◇ ((z ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3493 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3493 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3493.models_iff G M).mp hM
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
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e21
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e23 : False := by grind
      exact b0e23
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y ≠ y ∨ x = (k x y) := by
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
        have b1e28 : x = (k x y) := by grind
        clear b1e26
        have b1e50 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e54 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e50
        have b1e55 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e54
             have r₂ := b1e23
             grind)
          | exact resolve b1e54 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e56 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e57 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e56
          | exact resolve b1e56 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e56
        have b1e58 : False := by grind
        exact b1e58
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y ≠ y ∨ x = (k x y) := by
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
        have b2e25 : x = (k x y) := by grind
        clear b2e24
        have b2e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e812 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e75 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e21032 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e812 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e812
          | (have j0 := b2e812 x y
             grind)
          | exact resolve b2e812 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e812
        have b2e21041 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e21032
        have b2e21071 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e21041
             have r₂ := b2e22
             grind)
          | exact resolve b2e21041 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21041
        have b2e21085 : False := by grind
        exact b2e21085
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e24
          | exact resolve b3e24 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e28
          | exact resolve b3e28 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e49 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e52 : x = y ∨ y = (k x y) := by grind
        clear b3e49
        have b3e53 : y = (k x y) := by
          first
          | (have r₁ := b3e52
             have r₂ := b3e23
             grind)
          | exact resolve b3e52 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e52
        have b3e56 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e29
          | exact resolve b3e29 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e53
        have b3e57 : False := by grind
        exact b3e57
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e27
            | exact resolve b4e27 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e29 : False := by grind
          exact b4e29
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e68 : x = y ∨ y = (k x y) := by grind
          clear b5e63
          have b5e69 : y = (k x y) := by
            first
            | (have r₁ := b5e68
               have r₂ := b5e25
               grind)
            | exact resolve b5e68 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e68
          have b5e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e775 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e19233 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e775 x y
               have i₂ := b5e69
               grind)
            | exact superpose b5e69 b5e775
            | (have j0 := b5e775 x y
               grind)
            | exact resolve b5e775 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69 b5e775
          have b5e19242 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e19233
          have b5e19247 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e19242
               have r₂ := b5e24
               grind)
            | exact resolve b5e19242 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19242
          have b5e19261 : False := by grind
          exact b5e19261
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e24
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
        have b6e31 : (k x y) = (τ (σ x)) := by
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
        have b6e32 : x = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e71 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e73 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e71
        have b6e76 : y = (M.op x y) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e21
             grind)
          | exact resolve b6e73 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e79 : False := by grind
        exact b6e79
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e64 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e59
          have b7e65 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e66 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e14
            | exact resolve b7e14 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : y = (k x y) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e69
            | exact resolve b7e69 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e79 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e80 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e79
          have b7e82 : x = (M.op x y) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e21
               grind)
            | exact resolve b7e80 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e84 : False := by grind
          exact b7e84
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e733 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e88 x y
               grind)
            | exact superpose b8e88 b8e20
            | (have j1 := b8e88 x y
               grind)
            | exact resolve b8e20 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e780 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e733
               have r₂ := b8e24
               grind)
            | exact resolve b8e733 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e733
          have b8e784 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e780
               have r₂ := b8e23
               grind)
            | exact resolve b8e780 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e780
          have b8e840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e784
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e784
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e784 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e784
          have b8e841 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e840
          have b8e842 : y = (M.op x y) := by
            first
            | (have r₁ := b8e841
               have r₂ := b8e22
               grind)
            | exact resolve b8e841 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e841
          have b8e843 : False := by grind
          exact b8e843

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyy_x_pxy_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 X3 X4
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
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
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 (M.op (M.op X2 X3) X0) X3
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op y X0) x
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e696 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X0 X0)) = (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X1 X1) X0))) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b0e33 X1 (M.op x x) (M.op (M.op X1 X1) X0) X4 X5
           have i₂ := b0e37 X1 X0 x x
           grind)
        | exact superpose b0e37 b0e33
        | exact resolve b0e33 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e705 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op (M.op X0 X0) X0))) := by
        intro X0
        first
        | (have i₁ := b0e34 (M.op (M.op X0 X0) X0)
           have i₂ := b0e37 X0 X0 X0 X0
           grind)
        | exact superpose b0e37 b0e34
        | exact resolve b0e34 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e720 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op x (M.op y (M.op (M.op X1 X1) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e696 X0 X1 x x
           have i₂ := b0e42 (M.op (M.op X1 X1) X0) x x
           grind)
        | exact superpose b0e42 b0e696
        | exact resolve b0e696 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e696
      have b0e1387 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e46 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e46
        | exact resolve b0e46 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e1642 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
        first
        | (have i₁ := b0e1387 x
           have i₂ := b0e34 (M.op y x)
           grind)
        | exact superpose b0e34 b0e1387
        | exact resolve b0e1387 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e1692 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e42 (M.op y X0) x y
           have i₂ := b0e1387 X0
           grind)
        | exact superpose b0e1387 b0e42
        | exact resolve b0e42 b0e1387
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e1387
      have b0e1755 : (M.op x x) = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b0e1642
           have i₂ := b0e1692 x
           grind)
        | exact superpose b0e1692 b0e1642
        | exact resolve b0e1642 b0e1692
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1642 b0e1692
      have b0e1778 : y = (M.op x y) := by
        first
        | (have i₁ := b0e1755
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1755
        | exact resolve b0e1755 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1755
      have b0e22180 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e705 X0
           have i₂ := b0e720 X0 X0
           grind)
        | exact superpose b0e720 b0e705
        | exact resolve b0e705 b0e720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e705 b0e720
      have b0e23046 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e22180 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e22180
        | exact resolve b0e22180 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22180
      have b0e23262 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e23046
           grind)
        | exact superpose b0e23046 b0e18
        | exact resolve b0e18 b0e23046
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23046
      have b0e23290 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e23262
           have i₂ := b0e1778
           grind)
        | exact superpose b0e1778 b0e23262
        | exact resolve b0e23262 b0e1778
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1778 b0e23262
      have b0e23291 : False := by grind
      exact b0e23291
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e34 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op x (M.op y X0)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 X0
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op y X0) x
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 X0 (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1349 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e45 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e45
          | exact resolve b1e45 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e1584 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
          first
          | (have i₁ := b1e1349 x
             have i₂ := b1e34 (M.op y x)
             grind)
          | exact superpose b1e34 b1e1349
          | exact resolve b1e1349 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e1634 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e41 (M.op y X0) x y
             have i₂ := b1e1349 X0
             grind)
          | exact superpose b1e1349 b1e41
          | exact resolve b1e41 b1e1349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1349
        have b1e1695 : (M.op x x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b1e1584
             have i₂ := b1e1634 x
             grind)
          | exact superpose b1e1634 b1e1584
          | exact resolve b1e1584 b1e1634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1584 b1e1634
        have b1e1718 : y = (M.op x y) := by
          first
          | (have i₁ := b1e1695
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1695
          | exact resolve b1e1695 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1695
        have b1e1846 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e41 X0 y x
             have i₂ := b1e1718
             grind)
          | exact superpose b1e1718 b1e41
          | exact resolve b1e41 b1e1718
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e2728 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e1846 (M.op (M.op x (M.op y y)) x)
             have i₂ := b1e43 y x
             grind)
          | exact superpose b1e43 b1e1846
          | exact resolve b1e1846 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e1846
        have b1e2815 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b1e2728 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2728
          | exact resolve b1e2728 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2728
        have b1e2866 : y = (M.op y y) := by
          first
          | (have i₁ := b1e2815
             have i₂ := b1e1718
             grind)
          | exact superpose b1e1718 b1e2815
          | exact resolve b1e2815 b1e1718
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1718 b1e2815
        have b1e2950 : y = (k y y) := by grind
        clear b1e2866
        have b1e3986 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e59 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e59
          | (have j0 := b1e59 (σ x)
             grind)
          | (have r₁ := b1e59 (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e59 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e3992 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b1e3986
        have b1e3994 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have r₁ := b1e3992
             have r₂ := b1e21
             grind)
          | exact resolve b1e3992 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3992
        have b1e4006 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e3994
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e3994
          | exact resolve b1e3994 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3994
        have b1e4018 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e4006
             have i₂ := b1e2950
             grind)
          | exact superpose b1e2950 b1e4006
          | exact resolve b1e4006 b1e2950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2950 b1e4006
        have b1e4020 : False := by grind
        exact b1e4020
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e50 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ y = X0 ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e16 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 x X0
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e168 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e56 (σ X0)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X0)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e179 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e65
        have b2e195 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e179 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e179
          | exact resolve b2e179 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e179
        have b2e725 : y ≠ y ∨ x = y ∨ y = (k x x) := by
          first
          | (have i₁ := b2e50 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e50
          | (have j0 := b2e50 x
             grind)
          | (have r₁ := b2e50 x
             have r₂ := b2e20
             grind)
          | exact resolve b2e50 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e733 : y = (k x x) ∨ x = y := by grind
        clear b2e725
        have b2e37391 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e168 x
             grind)
          | exact superpose b2e168 b2e21
          | (have j1 := b2e168 x
             grind)
          | exact resolve b2e21 b2e168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e168
        have b2e81072 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e37391
             have i₂ := b2e733
             grind)
          | exact superpose b2e733 b2e37391
          | exact resolve b2e37391 b2e733
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37391
        have b2e81077 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
        clear b2e81072
        have b2e81121 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e195 x
             have i₂ := b2e81077
             grind)
          | exact superpose b2e81077 b2e195
          | exact resolve b2e195 b2e81077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e195 b2e81077
        have b2e81275 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e81121
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e81121
          | exact resolve b2e81121 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81121
        have b2e81346 : x = y ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e733
             have i₂ := b2e81275
             grind)
          | exact superpose b2e81275 b2e733
          | exact resolve b2e733 b2e81275
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e733 b2e81275
        have b2e81382 : x = y := by grind
        clear b2e81346
        have b2e81483 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e81382
             grind)
          | exact superpose b2e81382 b2e22
          | exact resolve b2e22 b2e81382
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81382
        have b2e81631 : False := by grind
        exact b2e81631
  · rcases eq_or_ne (M.op x x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : (M.op x x) = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e31 : (k x y) = (τ (σ x)) := by
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
        have b3e32 : x = (k x y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e50 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ x) X0
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = y ∨ (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e843 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e50 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e50
          | (have j0 := b3e50 (σ x)
             grind)
          | (have r₁ := b3e50 (σ x)
             have r₂ := b3e22
             grind)
          | exact resolve b3e50 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e845 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
        clear b3e843
        have b3e846 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e845
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e845
          | exact resolve b3e845 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e845
        have b3e864 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have j0 := b3e52 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e866 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e864
             have r₂ := b3e20
             grind)
          | exact resolve b3e864 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e864
        have b3e870 : x = (M.op x y) := by
          first
          | (have i₁ := b3e866
             have i₂ := b3e32
             grind)
          | exact superpose b3e32 b3e866
          | exact resolve b3e866 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e866
        have b3e1722 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e846
             grind)
          | exact superpose b3e846 b3e13
          | exact resolve b3e13 b3e846
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1736 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1722
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1722
          | exact resolve b3e1722 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1722
        have b3e2112 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e55 x
             have i₂ := b3e1736
             grind)
          | exact superpose b3e1736 b3e55
          | (have j0 := b3e55 x
             grind)
          | exact resolve b3e55 b3e1736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e1736
        have b3e2113 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e2112
             have r₂ := b3e20
             grind)
          | exact resolve b3e2112 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2112
        have b3e2171 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e2113
        have b3e3107 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e846
             have i₂ := b3e2171
             grind)
          | exact superpose b3e2171 b3e846
          | exact resolve b3e846 b3e2171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e846 b3e2171
        have b3e3110 : (σ x) = (σ y) := by grind
        clear b3e3107
        have b3e3817 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e3110
             grind)
          | exact superpose b3e3110 b3e19
          | exact resolve b3e19 b3e3110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3834 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e3817
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e3817
          | exact resolve b3e3817 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3817
        have b3e3838 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e3834
             have i₂ := b3e3110
             grind)
          | exact superpose b3e3110 b3e3834
          | exact resolve b3e3834 b3e3110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3110 b3e3834
        have b3e3842 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e3838
             have i₂ := b3e870
             grind)
          | exact superpose b3e870 b3e3838
          | exact resolve b3e3838 b3e870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e870 b3e3838
        have b3e3843 : False := by grind
        exact b3e3843
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : (M.op x x) = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e55 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = y ∨ (k X0 y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 y
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e826 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by
            first
            | (have j0 := b4e55 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e828 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e826
               have r₂ := b4e21
               grind)
            | exact resolve b4e826 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e826
          have b4e4542 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b4e57 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e4544 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e4542
               have r₂ := b4e23
               grind)
            | exact resolve b4e4542 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4542
          have b4e4551 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e4544
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e4544
            | exact resolve b4e4544 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4544
          have b4e4557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e4551
               have i₂ := b4e828
               grind)
            | exact superpose b4e828 b4e4551
            | exact resolve b4e4551 b4e828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e828 b4e4551
          have b4e4559 : False := by grind
          exact b4e4559
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : (M.op x x) = (M.op y y) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e30 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x x) X0)) := by
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
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op (M.op X2 X3) X0) X3
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X1) X1 X2
               have i₂ := b5e13 (M.op X2 X1) X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
            intro X0 X1 X2
            grind
          have b5e47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e50 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op x x) = X0 ∨ (k y X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e17 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 X0 x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) ≠ (M.op X3 X3) ∨ (M.op X3 X3) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e17 X3 X2
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X3 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e122 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op (M.op x x) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e167 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e47 X0 (M.op X1 (M.op (M.op X2 X1) (σ X0)))
               have i₂ := b5e35 X1 X2 (σ X0)
               grind)
            | exact superpose b5e35 b5e47
            | exact resolve b5e47 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e47
          have b5e168 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0))))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e167 X0 X1 X2
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e167
            | exact resolve b5e167 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167
          have b5e188 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e54 (σ X0)
               grind)
            | exact superpose b5e54 b5e19
            | (have j1 := b5e54 (σ X0)
               grind)
            | exact resolve b5e19 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e479 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op (M.op X0 X0) X0) X1 X2
               have i₂ := b5e32 X0 X0 X0 X0
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e485 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x x) (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op (M.op X0 X0) X0)
               have i₂ := b5e32 X0 X0 X0 X0
               grind)
            | exact superpose b5e32 b5e30
            | exact resolve b5e30 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e657 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x x) = (k y y) := by
            first
            | (have i₁ := b5e50 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e50
            | (have j0 := b5e50 x
               grind)
            | (have r₁ := b5e50 y
               have r₂ := b5e22
               grind)
            | exact resolve b5e50 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e668 : y = (M.op x x) ∨ (M.op x x) = (k y y) := by grind
          clear b5e657
          have b5e671 : (M.op x x) = (k y y) := by
            first
            | (have r₁ := b5e668
               have r₂ := b5e21
               grind)
            | exact resolve b5e668 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e668
          have b5e1719 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X0) X2)) ≠ (M.op X3 (M.op (M.op X4 X3) X5)) ∨ (M.op X0 (M.op (M.op X1 X0) X2)) = X5 ∨ (k X2 X5) = (M.op X2 X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e53 X0 X1 X2 X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e53
            | (have j0 := b5e53 X0 X1 X5 X2
               grind)
            | (have r₁ := b5e53 X1 X2 X0 X0
               have r₂ := b5e13 X0 X1 X2
               grind)
            | exact resolve b5e53 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e1783 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y (M.op (M.op x x) X0))) = (M.op y (M.op (M.op x x) (M.op (M.op X3 (M.op X2 X1)) X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e122 (M.op (M.op X3 (M.op X2 X1)) X0) X1 X2
               have i₂ := b5e122 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b5e122 b5e122
            | exact resolve b5e122 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122
          have b5e8683 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e33 x x (M.op X0 X0) X0
               have i₂ := b5e479 X0 x x
               grind)
            | exact superpose b5e479 b5e33
            | exact resolve b5e33 b5e479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e9756 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0) X0
               have i₂ := b5e8683 X0
               grind)
            | exact superpose b5e8683 b5e13
            | exact resolve b5e13 b5e8683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e12597 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X0 X0) X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X0 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e9756 X2 (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X0 X0) X0))
               have i₂ := b5e479 X0 (M.op X2 X2) X1
               grind)
            | exact superpose b5e479 b5e9756
            | exact resolve b5e9756 b5e479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e479 b5e9756
          have b5e12928 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X0)) = (M.op y (M.op (M.op x x) (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X0 X0) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e12597 X0 X1 X2
               have i₂ := b5e30 (M.op (M.op X1 (M.op X2 X2)) (M.op (M.op X0 X0) X0))
               grind)
            | exact superpose b5e30 b5e12597
            | exact resolve b5e12597 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e12597
          have b5e13055 : ∀ X0 X2 : G, (M.op (M.op X2 X2) (M.op X0 X0)) = (M.op X2 (M.op y (M.op (M.op x x) (M.op (M.op X0 X0) X0)))) := by
            intro X0 X2
            first
            | (have i₁ := b5e12928 X0 x X2
               have i₂ := b5e1783 (M.op (M.op X0 X0) X0) X2 X2 x
               grind)
            | exact superpose b5e1783 b5e12928
            | exact resolve b5e12928 b5e1783
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1783 b5e12928
          have b5e13078 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X2 X2) (M.op X0 X0)) := by
            intro X0 X2
            first
            | (have i₁ := b5e13055 X0 X2
               have i₂ := b5e485 X0
               grind)
            | exact superpose b5e485 b5e13055
            | exact resolve b5e13055 b5e485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e485 b5e13055
          have b5e14049 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
            intro X0
            grind
          clear b5e13078
          have b5e14200 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e14049 X0
               have i₂ := b5e8683 X0
               grind)
            | exact superpose b5e8683 b5e14049
            | exact resolve b5e14049 b5e8683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8683 b5e14049
          have b5e25822 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e188 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e188
          have b5e51680 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e25822 (M.op X0 X0)
               have i₂ := b5e14200 X0
               grind)
            | exact superpose b5e14200 b5e25822
            | (have j0 := b5e25822 (M.op X0 X0)
               grind)
            | exact resolve b5e25822 b5e14200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14200 b5e25822
          have b5e51688 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b5e51680 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51680
          have b5e173658 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = X2 ∨ (M.op X2 X2) = (k X2 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e1719 X0 X1 X2 x x X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1719
          have b5e173857 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e168 X0 x x
               have i₂ := b5e173658 x x (σ X0)
               grind)
            | exact superpose b5e173658 b5e168
            | (have j1 := b5e173658 X0 x (σ X0)
               grind)
            | exact resolve b5e168 b5e173658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168 b5e173658
          have b5e173956 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e173857 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e173857
            | (have j0 := b5e173857 X0
               grind)
            | exact resolve b5e173857 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e173857
          have b5e174081 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e173956 X0
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e173956
            | (have j0 := b5e173956 X0
               grind)
            | exact resolve b5e173956 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e173956
          have b5e175180 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e174081 y
               grind)
            | exact superpose b5e174081 b5e24
            | (have j1 := b5e174081 y
               grind)
            | exact resolve b5e24 b5e174081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e175339 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b5e175180
               have i₂ := b5e671
               grind)
            | exact superpose b5e671 b5e175180
            | exact resolve b5e175180 b5e671
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175180
          have b5e175359 : y = (M.op x x) ∨ (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e175339
               have i₂ := b5e671
               grind)
            | exact superpose b5e671 b5e175339
            | exact resolve b5e175339 b5e671
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e671 b5e175339
          have b5e175363 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b5e175359
               have r₂ := b5e21
               grind)
            | exact resolve b5e175359 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175359
          have b5e175368 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e175363
               have i₂ := b5e174081 x
               grind)
            | exact superpose b5e174081 b5e175363
            | (have j1 := b5e174081 x
               grind)
            | exact resolve b5e175363 b5e174081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e174081
          have b5e175420 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e175368
               have i₂ := b5e54 x
               grind)
            | exact superpose b5e54 b5e175368
            | (have j1 := b5e54 x
               grind)
            | exact resolve b5e175368 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e175368
          have b5e175424 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b5e175420
          have b5e175425 : x = (M.op x x) := by grind
          clear b5e175424
          have b5e175768 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e51688 x
               have i₂ := b5e175425
               grind)
            | exact superpose b5e175425 b5e51688
            | exact resolve b5e51688 b5e175425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51688
          have b5e178016 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e175363
               have i₂ := b5e175768
               grind)
            | exact superpose b5e175768 b5e175363
            | exact resolve b5e175363 b5e175768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175363 b5e175768
          have b5e178557 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e178016
               have i₂ := b5e175425
               grind)
            | exact superpose b5e175425 b5e178016
            | exact resolve b5e178016 b5e175425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175425 b5e178016
          have b5e178558 : False := by grind
          exact b5e178558
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e16 (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ x) X0
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e920 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e55 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e55
          | (have j0 := b6e55 (σ x)
             grind)
          | (have r₁ := b6e55 (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e55 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e921 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
        clear b6e920
        have b6e922 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e921
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e921
          | exact resolve b6e921 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e921
        have b6e1020 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e922
             grind)
          | exact superpose b6e922 b6e13
          | exact resolve b6e13 b6e922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1032 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1020
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1020
          | exact resolve b6e1020 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1020
        have b6e1119 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e59 x
             have i₂ := b6e1032
             grind)
          | exact superpose b6e1032 b6e59
          | (have j0 := b6e59 x
             grind)
          | exact resolve b6e59 b6e1032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e1032
        have b6e1120 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1119
             have r₂ := b6e20
             grind)
          | exact resolve b6e1119 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1119
        have b6e1151 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1120
        have b6e1230 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e922
             have i₂ := b6e1151
             grind)
          | exact superpose b6e1151 b6e922
          | exact resolve b6e922 b6e1151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e922 b6e1151
        have b6e1233 : (σ x) = (σ y) := by grind
        clear b6e1230
        have b6e1444 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1233
             grind)
          | exact superpose b6e1233 b6e13
          | exact resolve b6e13 b6e1233
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1233
        have b6e1457 : x = y := by
          first
          | (have i₁ := b6e1444
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1444
          | exact resolve b6e1444 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1444
        have b6e1784 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e1457
             grind)
          | exact superpose b6e1457 b6e21
          | exact resolve b6e21 b6e1457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1457
        have b6e1791 : False := by grind
        exact b6e1791
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X2 X2
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 (M.op (M.op X2 X3) X0) X3
               have i₂ := b7e13 X0 X3 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X1) X1 X2
               have i₂ := b7e13 (M.op X2 X1) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b7e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e17 X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 X0 (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e187 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e62 (σ X0)
               grind)
            | exact superpose b7e62 b7e19
            | (have j1 := b7e62 (σ X0)
               grind)
            | exact resolve b7e19 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e522 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op (M.op X0 X0) X0) X1 X2
               have i₂ := b7e36 X0 X0 X0 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e994 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e37 X0 X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) x
               have i₂ := b7e35 X0 X1 (M.op X1 X0) x
               grind)
            | exact superpose b7e35 b7e37
            | exact resolve b7e37 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e1134 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) (M.op (M.op X0 (M.op X1 X1)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e38 X0 X0 X1 (M.op X0 X0)
               have i₂ := b7e994 X0 X1
               grind)
            | exact superpose b7e994 b7e38
            | exact resolve b7e38 b7e994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e994
          have b7e1235 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b7e1134 x X1 X2
               have i₂ := b7e38 X2 x X1 X1
               grind)
            | exact superpose b7e38 b7e1134
            | exact resolve b7e1134 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e1134
          have b7e1309 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op X0 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X1 X1) X0 X0
               have i₂ := b7e1235 X0 X1
               grind)
            | exact superpose b7e1235 b7e13
            | exact resolve b7e13 b7e1235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1326 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
            intro X0
            grind
          have b7e1360 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1309 X0 X1
               have i₂ := b7e1235 X1 X1
               grind)
            | (have i₁ := b7e1309 X0 x
               have i₂ := b7e1235 (M.op x x) x
               grind)
            | exact superpose b7e1235 b7e1309
            | exact resolve b7e1309 b7e1235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1235 b7e1309
          have b7e3164 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e37 x x (M.op X0 X0) X0
               have i₂ := b7e522 X0 x x
               grind)
            | exact superpose b7e522 b7e37
            | exact resolve b7e37 b7e522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37 b7e522
          have b7e3645 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e3164 X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e3164
            | exact resolve b7e3164 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3671 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1360 X1 X0
               have i₂ := b7e3164 X0
               grind)
            | exact superpose b7e3164 b7e1360
            | exact resolve b7e1360 b7e3164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1360
          have b7e3672 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e1326 X0
               have i₂ := b7e3164 X0
               grind)
            | exact superpose b7e3164 b7e1326
            | exact resolve b7e1326 b7e3164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1326 b7e3164
          have b7e3754 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e61 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e61
            | (have j0 := b7e61 (σ x)
               grind)
            | (have r₁ := b7e61 (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e61 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e3761 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b7e3754
          have b7e3764 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have r₁ := b7e3761
               have r₂ := b7e23
               grind)
            | exact resolve b7e3761 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3761
          have b7e3770 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e3764
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e3764
            | exact resolve b7e3764 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3764
          have b7e6709 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e3671 X2 (M.op X2 X2)
               have i₂ := b7e13 (M.op X2 X2) X0 X1
               grind)
            | exact superpose b7e13 b7e3671
            | exact resolve b7e3671 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3671
          have b7e6848 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e6709 X0 X1 X2
               have i₂ := b7e3645 X0 X1 (M.op X2 X2)
               grind)
            | exact superpose b7e3645 b7e6709
            | exact resolve b7e6709 b7e3645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3645 b7e6709
          have b7e19914 : (σ (k y y)) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e187 x
               have i₂ := b7e3770
               grind)
            | exact superpose b7e3770 b7e187
            | exact resolve b7e187 b7e3770
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3770
          have b7e20090 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e187 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e187
          have b7e40667 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e20090 (M.op X0 X0)
               have i₂ := b7e3672 X0
               grind)
            | exact superpose b7e3672 b7e20090
            | (have j0 := b7e20090 (M.op X0 X0)
               grind)
            | exact resolve b7e20090 b7e3672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20090
          have b7e40677 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b7e40667 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40667
          have b7e77522 : (k y y) = (τ (σ (k x x))) ∨ (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e19914
               grind)
            | exact superpose b7e19914 b7e14
            | exact resolve b7e14 b7e19914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e19914
          have b7e77532 : (σ x) = (σ (k y y)) ∨ (k y y) = (k x x) := by
            first
            | (have i₁ := b7e77522
               have i₂ := b7e14 (k x x)
               grind)
            | exact superpose b7e14 b7e77522
            | exact resolve b7e77522 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77522
          have b7e77581 : (k y y) = (τ (σ x)) ∨ (k y y) = (k x x) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e77532
               grind)
            | exact superpose b7e77532 b7e14
            | exact resolve b7e14 b7e77532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77532
          have b7e77592 : (k y y) = (k x x) ∨ x = (k y y) := by
            first
            | (have i₁ := b7e77581
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e77581
            | exact resolve b7e77581 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77581
          have b7e77633 : (M.op y y) = (k x x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e77592
               have i₂ := b7e62 y
               grind)
            | exact superpose b7e62 b7e77592
            | (have j1 := b7e62 y
               grind)
            | exact resolve b7e77592 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77592
          have b7e116607 : (M.op x x) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e62 x
               have i₂ := b7e77633
               grind)
            | exact superpose b7e77633 b7e62
            | (have j0 := b7e62 x
               grind)
            | exact resolve b7e62 b7e77633
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e116613 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b7e116607
               have r₂ := b7e22
               grind)
            | exact resolve b7e116607 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116607
          have b7e116662 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e40677 y
               have i₂ := b7e116613
               grind)
            | exact superpose b7e116613 b7e40677
            | exact resolve b7e40677 b7e116613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116613
          have b7e116694 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e116662
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e116662
            | exact resolve b7e116662 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116662
          have b7e116699 : x = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b7e116694
               have r₂ := b7e23
               grind)
            | exact resolve b7e116694 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116694
          have b7e116810 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) x)) ∨ x = (M.op x x) := by
            intro X0 X1
            first
            | (have i₁ := b7e6848 X0 X1 y
               have i₂ := b7e116699
               grind)
            | exact superpose b7e116699 b7e6848
            | exact resolve b7e6848 b7e116699
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6848 b7e116699
          have b7e117012 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e116810 x x
               have i₂ := b7e13 x x x
               grind)
            | exact superpose b7e13 b7e116810
            | exact resolve b7e116810 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116810
          have b7e117013 : x = (M.op x x) := by grind
          clear b7e117012
          have b7e117133 : x = (k x x) := by
            first
            | (have i₁ := b7e3672 x
               have i₂ := b7e117013
               grind)
            | exact superpose b7e117013 b7e3672
            | exact resolve b7e3672 b7e117013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3672
          have b7e117522 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e77633
               have i₂ := b7e117133
               grind)
            | exact superpose b7e117133 b7e77633
            | exact resolve b7e77633 b7e117133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77633 b7e117133
          have b7e117554 : y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b7e117522
          have b7e124913 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e40677 y
               have i₂ := b7e117554
               grind)
            | exact superpose b7e117554 b7e40677
            | exact resolve b7e40677 b7e117554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40677 b7e117554
          have b7e125050 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e124913
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e124913
            | exact resolve b7e124913 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124913
          have b7e125083 : x = (M.op y y) := by
            first
            | (have r₁ := b7e125050
               have r₂ := b7e23
               grind)
            | exact resolve b7e125050 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125050
          have b7e125098 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e125083
               grind)
            | exact superpose b7e125083 b7e22
            | exact resolve b7e22 b7e125083
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125083
          have b7e125498 : False := by grind
          exact b7e125498
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X2 X3 X4
               have i₂ := b8e13 X2 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 X2 X2
               have i₂ := b8e13 X2 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op (M.op X2 X3) X0) X3
               have i₂ := b8e13 X0 X3 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X2 X1) X1 X2
               have i₂ := b8e13 (M.op X2 X1) X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b8e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e32
            | exact resolve b8e32 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X2
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e90 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (M.op (σ y) (σ y))
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e93 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e22
               have i₂ := b8e18 y X0
               grind)
            | (have i₁ := b8e22
               have i₂ := b8e18 X0 y
               grind)
            | exact superpose b8e18 b8e22
            | (have j1 := b8e18 y X0
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x (M.op y y)
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ (k X0 x) = (M.op x X0) ∨ (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 x
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 x x
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 X0 x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e105 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e110 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b8e45
          have b8e123 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e110 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e110
            | exact resolve b8e110 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e157 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e58 (σ X0)
               grind)
            | exact superpose b8e58 b8e19
            | (have j1 := b8e58 (σ X0)
               grind)
            | exact resolve b8e19 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e279 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op (M.op (M.op X3 (M.op X4 (M.op (M.op X5 X4) X6))) X2) (M.op (M.op X3 (M.op X4 (M.op (M.op X5 X4) X6))) X2)) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b8e35 X4 X5 X6 (M.op (M.op X3 (M.op X4 (M.op (M.op X5 X4) X6))) X2)
               have i₂ := b8e34 (M.op X4 (M.op (M.op X5 X4) X6)) X3 X2 X0 X1
               grind)
            | (have i₁ := b8e35 X4 X5 X6 (M.op (M.op X3 (M.op X4 (M.op (M.op X5 X4) X6))) X2)
               have i₂ := b8e34 X0 X1 X2 (M.op X4 (M.op (M.op X5 X4) X6)) X3
               grind)
            | exact superpose b8e34 b8e35
            | exact resolve b8e35 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e307 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X3 X4))) X0) (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X3 X4))) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 (M.op (M.op X1 (M.op (M.op X2 X1) (M.op X3 X4))) X0) X4 X3
               have i₂ := b8e35 X1 X2 (M.op X3 X4) X0
               grind)
            | exact superpose b8e35 b8e13
            | exact resolve b8e13 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e308 : ∀ X0 X3 X4 : G, (M.op X4 (M.op X0 X0)) = (M.op (M.op X3 X4) (M.op X0 X0)) := by
            intro X0 X3 X4
            first
            | (have i₁ := b8e307 X0 x x X3 X4
               have i₂ := b8e38 X0 x (M.op x x) (M.op X3 X4)
               grind)
            | exact superpose b8e38 b8e307
            | exact resolve b8e307 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e307
          have b8e312 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X6 (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op (M.op (M.op X5 X4) X6) (M.op X2 X2)) := by
            intro X0 X1 X2 X4 X5 X6
            first
            | (have i₁ := b8e279 X0 X1 X2 x X4 X5 X6
               have i₂ := b8e38 X2 x X4 (M.op (M.op X5 X4) X6)
               grind)
            | exact superpose b8e38 b8e279
            | exact resolve b8e279 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e279
          have b8e317 : ∀ X0 X1 X2 X6 : G, (M.op X6 (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X6 (M.op X2 X2)) := by
            intro X0 X1 X2 X6
            first
            | (have i₁ := b8e312 X0 X1 X2 x x X6
               have i₂ := b8e308 X2 (M.op x x) X6
               grind)
            | (have i₁ := b8e312 X0 X1 X0 x x X6
               have i₂ := b8e308 X0 x (M.op (M.op x x) X6)
               grind)
            | exact superpose b8e308 b8e312
            | exact resolve b8e312 b8e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e312
          have b8e353 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X0 X0) X1 X2
               have i₂ := b8e308 X0 X0 X0
               grind)
            | exact superpose b8e308 b8e13
            | exact resolve b8e13 b8e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e358 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
            intro X0
            grind
          have b8e367 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e353 X0 X1 x
               have i₂ := b8e308 X0 x X1
               grind)
            | (have i₁ := b8e353 X0 X1 x
               have i₂ := b8e308 X0 x (M.op x X1)
               grind)
            | exact superpose b8e308 b8e353
            | exact resolve b8e353 b8e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e353
          have b8e471 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op (M.op X0 X0) X0) X1 X2
               have i₂ := b8e36 X0 X0 X0 X0
               grind)
            | exact superpose b8e36 b8e13
            | exact resolve b8e13 b8e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e817 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
            first
            | (have j0 := b8e93 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93
          have b8e4296 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e37 x x (M.op X0 X0) X0
               have i₂ := b8e471 X0 x x
               grind)
            | exact superpose b8e471 b8e37
            | exact resolve b8e37 b8e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37 b8e471
          have b8e4497 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e367 X0 X1
               have i₂ := b8e4296 X0
               grind)
            | exact superpose b8e4296 b8e367
            | exact resolve b8e367 b8e4296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e4498 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e358 X0
               have i₂ := b8e4296 X0
               grind)
            | exact superpose b8e4296 b8e358
            | exact resolve b8e358 b8e4296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e4504 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) X0
               have i₂ := b8e4296 X0
               grind)
            | exact superpose b8e4296 b8e13
            | exact resolve b8e13 b8e4296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4589 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have j0 := b8e90 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e4590 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e4589
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e4589
            | exact resolve b8e4589 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4589
          have b8e4776 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op X3 (M.op X0 (M.op (M.op X1 X0) X2)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e4497 X0 X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e4497
            | exact resolve b8e4497 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4497
          have b8e8620 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X3 X3)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X2 X1) X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e4504 X0 (M.op X3 X3)
               have i₂ := b8e317 X1 X2 X3 (M.op X0 X0)
               grind)
            | exact superpose b8e317 b8e4504
            | exact resolve b8e4504 b8e317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e317 b8e4504
          have b8e8898 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X3)) = (M.op (M.op X3 X3) (M.op X3 X3)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e8620 x X1 X2 X3
               have i₂ := b8e4776 X1 X2 X3 (M.op x x)
               grind)
            | exact superpose b8e4776 b8e8620
            | exact resolve b8e8620 b8e4776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4776 b8e8620
          have b8e8973 : ∀ X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X3)) = (M.op X3 (M.op X3 X3)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e8898 X1 X2 X3
               have i₂ := b8e308 X3 X3 X3
               grind)
            | (have i₁ := b8e8898 X1 X2 x
               have i₂ := b8e308 x X3 (M.op x x)
               grind)
            | exact superpose b8e308 b8e8898
            | exact resolve b8e8898 b8e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e308 b8e8898
          have b8e12975 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e84 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e12976 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e12975 X0 X1
               have j1 := b8e105 X1 X0
               grind)
            | (have r₁ := b8e12975 X1 X1
               have r₂ := b8e105 X0 X1
               grind)
            | (have r₁ := b8e12975 X1 X1
               have r₂ := b8e105 X0 X1
               grind)
            | (have r₁ := b8e12975 (M.op (M.op X1 X1) (M.op X1 X1)) X1
               have r₂ := b8e105 X0 (M.op X1 X1)
               grind)
            | exact resolve b8e12975 b8e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105 b8e12975
          have b8e20525 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e157 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157
          have b8e20765 : y = (k y (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e123 y
               have i₂ := b8e4590
               grind)
            | exact superpose b8e4590 b8e123
            | exact resolve b8e123 b8e4590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e20874 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e20765
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e20765
            | exact resolve b8e20765 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20765
          have b8e20891 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e20525 (M.op X0 X0)
               have i₂ := b8e4498 X0
               grind)
            | exact superpose b8e4498 b8e20525
            | (have j0 := b8e20525 (M.op X0 X0)
               grind)
            | exact resolve b8e20525 b8e4498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e20895 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e20525 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e20525
            | (have j0 := b8e20525 (τ X0)
               grind)
            | exact resolve b8e20525 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e20525
          have b8e20897 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b8e20891 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20891
          have b8e20900 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e20895 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e20895
            | (have j0 := b8e20895 X0
               grind)
            | exact resolve b8e20895 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20895
          have b8e20903 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e20900 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e20900
            | (have j0 := b8e20900 X0
               grind)
            | exact resolve b8e20900 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20900
          have b8e22309 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e20903 (τ X0)
               have i₂ := b8e48 X0 X0
               grind)
            | exact superpose b8e48 b8e20903
            | (have j0 := b8e20903 (τ X0)
               grind)
            | exact resolve b8e20903 b8e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e35847 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e20874
               grind)
            | exact superpose b8e20874 b8e20
            | exact resolve b8e20 b8e20874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20874
          have b8e35991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e35847
               have i₂ := b8e817
               grind)
            | exact superpose b8e817 b8e35847
            | exact resolve b8e35847 b8e817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35847
          have b8e35995 : x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b8e35991
          have b8e36536 : x ≠ (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e35995
               grind)
            | exact superpose b8e35995 b8e22
            | exact resolve b8e22 b8e35995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36587 : x = (k x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e4498 y
               have i₂ := b8e35995
               grind)
            | exact superpose b8e35995 b8e4498
            | exact resolve b8e4498 b8e35995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35995
          have b8e37440 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e12976 x x
               have i₂ := b8e36587
               grind)
            | exact superpose b8e36587 b8e12976
            | (have j0 := b8e12976 x x
               grind)
            | exact resolve b8e12976 b8e36587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12976 b8e36587
          have b8e37441 : x = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e37440
          have b8e37447 : y = (M.op x y) := by
            first
            | (have r₁ := b8e37441
               have r₂ := b8e36536
               grind)
            | exact resolve b8e37441 b8e36536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36536 b8e37441
          have b8e37552 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 y x
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e13
            | exact resolve b8e13 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37608 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e8973 y x X0
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e8973
            | exact resolve b8e8973 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8973
          have b8e59854 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e22309 (M.op X0 X0)
               have i₂ := b8e4498 X0
               grind)
            | exact superpose b8e4498 b8e22309
            | (have j0 := b8e22309 (M.op X0 X0)
               grind)
            | exact resolve b8e22309 b8e4498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22309
          have b8e59861 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b8e59854 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59854
          have b8e59866 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op y (M.op y (τ (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b8e59861 X0
               have i₂ := b8e37552 (τ (M.op X0 X0))
               grind)
            | exact superpose b8e37552 b8e59861
            | exact resolve b8e59861 b8e37552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37552 b8e59861
          have b8e59925 : (τ (σ x)) = (M.op y (M.op y (τ (σ x)))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e59866 (σ y)
               have i₂ := b8e4590
               grind)
            | exact superpose b8e4590 b8e59866
            | exact resolve b8e59866 b8e4590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59866
          have b8e60071 : x = (M.op y (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e59925
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e59925
            | exact resolve b8e59925 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59925
          have b8e60105 : x = (M.op x (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e60071
               have i₂ := b8e37608 x
               grind)
            | exact superpose b8e37608 b8e60071
            | exact resolve b8e60071 b8e37608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37608 b8e60071
          have b8e60108 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e60105
               have i₂ := b8e4296 x
               grind)
            | exact superpose b8e4296 b8e60105
            | exact resolve b8e60105 b8e4296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4296 b8e60105
          have b8e65924 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e60108
               grind)
            | exact superpose b8e60108 b8e20
            | exact resolve b8e20 b8e60108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60108
          have b8e65960 : (σ y) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e65924
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e65924
            | exact resolve b8e65924 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65924
          have b8e65982 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e65960
               have i₂ := b8e817
               grind)
            | exact superpose b8e817 b8e65960
            | exact resolve b8e65960 b8e817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e817 b8e65960
          have b8e65988 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e65982
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e65982
            | exact resolve b8e65982 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65982
          have b8e65989 : x = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e65988
          have b8e66079 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e4498 y
               have i₂ := b8e65989
               grind)
            | exact superpose b8e65989 b8e4498
            | exact resolve b8e4498 b8e65989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4498 b8e65989
          have b8e66194 : x = (M.op x x) := by
            first
            | (have j1 := b8e20903 x
               grind)
            | (have r₁ := b8e66079
               have r₂ := b8e20903 x
               grind)
            | exact resolve b8e66079 b8e20903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20903 b8e66079
          have b8e66238 : x ≠ y := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e66194
               grind)
            | exact superpose b8e66194 b8e21
            | exact resolve b8e21 b8e66194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66338 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20897 x
               have i₂ := b8e66194
               grind)
            | exact superpose b8e66194 b8e20897
            | exact resolve b8e20897 b8e66194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66356 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e66194
               grind)
            | exact superpose b8e66194 b8e13
            | exact resolve b8e13 b8e66194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66194
          have b8e67601 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e66338
               grind)
            | exact superpose b8e66338 b8e23
            | exact resolve b8e23 b8e66338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66338
          have b8e70196 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e66356 y
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e66356
            | exact resolve b8e66356 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66356
          have b8e70751 : y = (M.op y y) := by
            first
            | (have i₁ := b8e70196
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e70196
            | exact resolve b8e70196 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70196
          have b8e70922 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e103 y
               have i₂ := b8e70751
               grind)
            | exact superpose b8e70751 b8e103
            | (have j0 := b8e103 y
               grind)
            | (have r₁ := b8e103 y
               have r₂ := b8e70751
               grind)
            | exact resolve b8e103 b8e70751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e70994 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e20897 y
               have i₂ := b8e70751
               grind)
            | exact superpose b8e70751 b8e20897
            | exact resolve b8e20897 b8e70751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20897 b8e70751
          have b8e71128 : (M.op x y) = (k y x) ∨ x = y := by grind
          clear b8e70922
          have b8e71194 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e71128
               have r₂ := b8e66238
               grind)
            | exact resolve b8e71128 b8e66238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66238 b8e71128
          have b8e71228 : y = (k y x) := by
            first
            | (have i₁ := b8e71194
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e71194
            | exact resolve b8e71194 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71194
          have b8e71855 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e4590
               have i₂ := b8e70994
               grind)
            | exact superpose b8e70994 b8e4590
            | exact resolve b8e4590 b8e70994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4590 b8e70994
          have b8e72073 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e71855
               have r₂ := b8e67601
               grind)
            | exact resolve b8e71855 b8e67601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67601 b8e71855
          have b8e72112 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e72073
               have i₂ := b8e71228
               grind)
            | exact superpose b8e71228 b8e72073
            | exact resolve b8e72073 b8e71228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71228 b8e72073
          have b8e72378 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e72112
               grind)
            | exact superpose b8e72112 b8e20
            | exact resolve b8e20 b8e72112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72112
          have b8e72451 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e72378
               have i₂ := b8e37447
               grind)
            | exact superpose b8e37447 b8e72378
            | exact resolve b8e72378 b8e37447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37447 b8e72378
          have b8e72452 : False := by grind
          exact b8e72452
