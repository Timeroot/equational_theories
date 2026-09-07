import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
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
        have b1e57 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e60 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e57
        have b1e61 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e60
             have r₂ := b1e23
             grind)
          | exact resolve b1e60 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e62 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e63 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e62
          | exact resolve b1e62 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e62
        have b1e64 : False := by grind
        exact b1e64
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
        have b2e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e769 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e13543 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e769 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e769
          | (have j0 := b2e769 x y
             grind)
          | exact resolve b2e769 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e769
        have b2e13550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e13543
        have b2e13581 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e13550
             have r₂ := b2e22
             grind)
          | exact resolve b2e13550 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13550
        have b2e13597 : False := by grind
        exact b2e13597
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
        have b3e48 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e51 : x = y ∨ y = (k x y) := by grind
        clear b3e48
        have b3e52 : y = (k x y) := by
          first
          | (have r₁ := b3e51
             have r₂ := b3e23
             grind)
          | exact resolve b3e51 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e51
        have b3e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e29
          | exact resolve b3e29 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e52
        have b3e56 : False := by grind
        exact b3e56
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
          have b5e56 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e59 : x = y ∨ y = (k x y) := by grind
          clear b5e56
          have b5e60 : y = (k x y) := by
            first
            | (have r₁ := b5e59
               have r₂ := b5e25
               grind)
            | exact resolve b5e59 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e59
          have b5e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e750 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e13561 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e750 x y
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e750
            | (have j0 := b5e750 x y
               grind)
            | exact resolve b5e750 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e750
          have b5e13567 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e13561
          have b5e13570 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e13567
               have r₂ := b5e24
               grind)
            | exact resolve b5e13567 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13567
          have b5e13585 : False := by grind
          exact b5e13585
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
        have b6e62 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e64 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e62
        have b6e67 : y = (M.op x y) := by
          first
          | (have r₁ := b6e64
             have r₂ := b6e21
             grind)
          | exact resolve b6e64 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e70 : False := by grind
        exact b6e70
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
          have b7e52 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e55 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e52
          have b7e56 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e25
               grind)
            | exact resolve b7e55 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e55
          have b7e57 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e56
            | exact resolve b7e56 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e14
            | exact resolve b7e14 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : y = (k x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e70 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e71 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e70
          have b7e73 : x = (M.op x y) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e75 : False := by grind
          exact b7e75
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e715 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e56 x y
               grind)
            | exact superpose b8e56 b8e20
            | (have j1 := b8e56 x y
               grind)
            | exact resolve b8e20 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e769 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e715
               have r₂ := b8e24
               grind)
            | exact resolve b8e715 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e715
          have b8e774 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e769
               have r₂ := b8e23
               grind)
            | exact resolve b8e769 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e769
          have b8e776 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e774
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e774
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e774 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e774
          have b8e777 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e776
          have b8e778 : y = (M.op x y) := by
            first
            | (have r₁ := b8e777
               have r₂ := b8e22
               grind)
            | exact resolve b8e777 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e777
          have b8e779 : False := by grind
          exact b8e779

/-- `Equation3566`: `x ◇ y = y ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_y_pyx_Equation3566 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3566 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3566.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e27 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X2 X0) X1) X3 X1
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e29 X0 X1 X2 X3
           have i₂ := b0e11 X1 X3 X0
           grind)
        | exact superpose b0e11 b0e29
        | exact resolve b0e29 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e35 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op (M.op y X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op y X0) X1 X0
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e11
        | exact resolve b0e11 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 X1
           have i₂ := b0e11 X0 X1 y
           grind)
        | exact superpose b0e11 b0e35
        | exact resolve b0e35 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e40 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 y
           grind)
        | (have r₁ := b0e14 X0 y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ y)
           grind)
        | (have r₁ := b0e14 X0 (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e43 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b0e40 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e44 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e21 X0 y
           have i₂ := b0e43 (τ X0)
           grind)
        | exact superpose b0e43 b0e21
        | exact resolve b0e21 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e43
      have b0e45 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e44 X0
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e44
        | exact resolve b0e44 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e44
      have b0e65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e37 X0 X1
           grind)
        | exact superpose b0e37 b0e11
        | exact resolve b0e11 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op X0 (M.op y X0)) ∨ (M.op (M.op y X0) X1) = (k X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (M.op y X0)
           have i₂ := b0e37 X0 (M.op y X0)
           grind)
        | exact superpose b0e37 b0e14
        | (have j0 := b0e14 X1 (M.op y X0)
           grind)
        | exact resolve b0e14 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e72 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (k X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e71 X0 X1
           grind)
        | (have r₁ := b0e71 X0 X1
           have r₂ := b0e27 X0
           grind)
        | exact resolve b0e71 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e71
      have b0e75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e72 X0 X1
           have i₂ := b0e37 X0 X1
           grind)
        | exact superpose b0e37 b0e72
        | exact resolve b0e72 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e72
      have b0e121 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X0
           have i₂ := b0e65 (M.op X0 X1) X2
           grind)
        | exact superpose b0e65 b0e11
        | exact resolve b0e11 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e155 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ (M.op X0 (M.op (M.op X1 X2) X0)) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 X3 (M.op (M.op X1 X2) X0)
           have i₂ := b0e31 X2 X0 X1 (M.op (M.op X1 X2) X0)
           grind)
        | exact superpose b0e31 b0e14
        | (have j0 := b0e14 X3 (M.op (M.op X1 X2) X0)
           grind)
        | exact resolve b0e14 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e169 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e155 X0 X1 X2 X3
           grind)
        | (have r₁ := b0e155 X1 X1 X2 X3
           have r₂ := b0e65 (M.op X1 X2) X1
           grind)
        | exact resolve b0e155 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65 b0e155
      have b0e176 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op (M.op X1 X2) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e169 X0 X1 X2 X3
           have i₂ := b0e31 X2 X0 X1 X3
           grind)
        | exact superpose b0e31 b0e169
        | exact resolve b0e169 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e169
      have b0e177 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op X2 X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e176 X0 x X2 X3
           have i₂ := b0e121 x X2 X0
           grind)
        | exact superpose b0e121 b0e176
        | exact resolve b0e176 b0e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e121 b0e176
      have b0e688 : ∀ X0 X1 : G, (σ (k X1 (M.op y (τ X0)))) = (k (σ X1) (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 (M.op y (τ X0))
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e17
        | exact resolve b0e17 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e696 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (k X1 (M.op y (τ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e688 X0 X1
           have i₂ := b0e177 X0 (σ y) (σ X1)
           grind)
        | exact superpose b0e177 b0e688
        | exact resolve b0e688 b0e177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e177 b0e688
      have b0e699 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e696 X0 X1
           have i₂ := b0e75 (τ X0) X1
           grind)
        | exact superpose b0e75 b0e696
        | exact resolve b0e696 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75 b0e696
      have b0e994 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e699 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e699
        | exact resolve b0e699 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e699
      have b0e1729 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e994 x y
           grind)
        | exact superpose b0e994 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e994 x y
           grind)
        | exact resolve b0e18 b0e994
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e994
      have b0e1754 : False := by grind
      exact b0e1754
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
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
        have b1e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op (M.op X2 X0) X1) X3 X1
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e27 X0 X1 X2 X3
             have i₂ := b1e12 X1 X3 X0
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e38 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
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
        have b1e39 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e45 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e46 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e45
          | exact resolve b1e45 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e39 x
             grind)
          | exact superpose b1e39 b1e46
          | exact resolve b1e46 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e46
        have b1e50 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e13
          | exact resolve b1e13 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : y = (M.op y x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e50
          | exact resolve b1e50 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e66 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x X0 y
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e12
          | exact resolve b1e12 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e66 X0
             have i₂ := b1e25 X0
             grind)
          | exact superpose b1e25 b1e66
          | exact resolve b1e66 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e66
        have b1e135 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (M.op x x)
             have i₂ := b1e29 x X0 x X1
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e277 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e135 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e135
          | exact resolve b1e135 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e135
        have b1e488 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 (σ x)
             have i₂ := b1e277
             grind)
          | exact superpose b1e277 b1e15
          | (have j0 := b1e15 X0 (σ x)
             grind)
          | (have r₁ := b1e15 X0 (σ x)
             have r₂ := b1e277
             grind)
          | exact resolve b1e15 b1e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e495 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e488 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e488
        have b1e727 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 x
             have i₂ := b1e495 (σ X0)
             grind)
          | exact superpose b1e495 b1e18
          | exact resolve b1e18 b1e495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e495
        have b1e1028 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e277
             have i₂ := b1e727 x
             grind)
          | exact superpose b1e727 b1e277
          | exact resolve b1e277 b1e727
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e727
        have b1e1088 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e1028
             grind)
          | exact superpose b1e1028 b1e13
          | exact resolve b1e13 b1e1028
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1028
        have b1e1105 : x = (k x x) := by
          first
          | (have i₁ := b1e1088
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1088
          | exact resolve b1e1088 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1088
        have b1e1183 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1105
             grind)
          | exact superpose b1e1105 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1105
        have b1e1184 : x = (M.op x x) := by grind
        clear b1e1183
        have b1e1190 : x = (M.op y x) := by
          first
          | (have i₁ := b1e1184
             have i₂ := b1e67 x
             grind)
          | exact superpose b1e67 b1e1184
          | exact resolve b1e1184 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e1184
        have b1e1196 : x = y := by
          first
          | (have i₁ := b1e1190
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e1190
          | exact resolve b1e1190 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e1190
        have b1e1283 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e277
             have i₂ := b1e1196
             grind)
          | exact superpose b1e1196 b1e277
          | exact resolve b1e277 b1e1196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e277 b1e1196
        have b1e1293 : False := by grind
        exact b1e1293
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
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
        have b2e38 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e511 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e57 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e513 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e511 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511
        have b2e1109 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e513 y
             have i₂ := b2e38 y
             grind)
          | exact superpose b2e38 b2e513
          | (have j0 := b2e513 y
             grind)
          | exact resolve b2e513 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e513
        have b2e1118 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b2e1109
             have r₂ := b2e21
             grind)
          | exact resolve b2e1109 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1109
        have b2e1132 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1118
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1118
          | exact resolve b2e1118 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1118
        have b2e1133 : False := by grind
        exact b2e1133
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e36 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b3e37 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e36 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e39 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e37 (σ X0)
             grind)
          | exact superpose b3e37 b3e18
          | exact resolve b3e18 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e695 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e39 y
             grind)
          | exact superpose b3e39 b3e22
          | exact resolve b3e22 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e736 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e695
             grind)
          | exact superpose b3e695 b3e13
          | exact resolve b3e13 b3e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e695
        have b3e749 : y = (k y y) := by
          first
          | (have i₁ := b3e736
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e736
          | exact resolve b3e736 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e736
        have b3e782 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e749
             grind)
          | exact superpose b3e749 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e749
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e749
        have b3e783 : y = (M.op y y) := by grind
        clear b3e782
        have b3e787 : False := by grind
        exact b3e787
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X2 X0) X1) X3 X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e33 X0 X1 X2 X3
               have i₂ := b4e13 X1 X3 X0
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e36 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X1 X0) x) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 (M.op (M.op x X0) x)
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e31
            | exact resolve b4e31 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op (M.op x X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op x X0) X1 X0
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 X1
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e41 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e36 X0 x
               have i₂ := b4e35 X0 x x (M.op X0 x)
               grind)
            | exact superpose b4e35 b4e36
            | exact resolve b4e36 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e40 X0 X1
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e80 : x = (M.op x x) := by
            first
            | (have i₁ := b4e41 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e99 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e80
               grind)
            | exact superpose b4e80 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e80
               grind)
            | exact resolve b4e16 b4e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e101 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e99 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e128 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
            intro X0 X1 X4
            first
            | (have i₁ := b4e35 X0 X1 (M.op x x) X4
               have i₂ := b4e35 x X0 x X1
               grind)
            | exact superpose b4e35 b4e35
            | exact resolve b4e35 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e136 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ (M.op X0 (M.op (M.op X1 X2) X0)) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16 X3 (M.op (M.op X1 X2) X0)
               have i₂ := b4e35 X2 X0 X1 (M.op (M.op X1 X2) X0)
               grind)
            | exact superpose b4e35 b4e16
            | (have j0 := b4e16 X3 (M.op (M.op X1 X2) X0)
               grind)
            | exact resolve b4e16 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e144 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e136 X0 X1 X2 X3
               grind)
            | (have r₁ := b4e136 X1 X1 X2 X3
               have r₂ := b4e45 (M.op X1 X2) X1
               grind)
            | exact resolve b4e136 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e136
          have b4e146 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e144 X0 X1 X2 X3
               have i₂ := b4e35 X2 X0 X1 X3
               grind)
            | exact superpose b4e35 b4e144
            | exact resolve b4e144 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e144
          have b4e147 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op X2 X0)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e146 X0 x X2 X3
               have i₂ := b4e128 x X2 X0
               grind)
            | exact superpose b4e128 b4e146
            | exact resolve b4e146 b4e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128 b4e146
          have b4e183 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e147 (σ x) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e147
            | exact resolve b4e147 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147
          have b4e651 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e183 (σ X0)
               grind)
            | exact superpose b4e183 b4e19
            | exact resolve b4e19 b4e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e183
          have b4e655 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e651 X0
               have i₂ := b4e101 X0
               grind)
            | exact superpose b4e101 b4e651
            | exact resolve b4e651 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101 b4e651
          have b4e754 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e655 y
               grind)
            | exact superpose b4e655 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e655 y
               grind)
            | exact resolve b4e20 b4e655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e655
          have b4e771 : False := by grind
          exact b4e771
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X2 X0) X1) X3 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e32 X0 X1 X2 X3
               have i₂ := b5e13 X1 X3 X0
               grind)
            | exact superpose b5e13 b5e32
            | exact resolve b5e32 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e35 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X1 X0) x) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e31 (M.op (M.op x X0) x)
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op (M.op x X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op x X0) X1 X0
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e39 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 X0 X1
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e37
            | exact resolve b5e37 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e40 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e35 X0 x
               have i₂ := b5e34 X0 x x (M.op X0 x)
               grind)
            | exact superpose b5e34 b5e35
            | exact resolve b5e35 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e39 X0 X1
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e75 : x = (M.op x x) := by
            first
            | (have i₁ := b5e40 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40
            | exact resolve b5e40 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e94 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e75
               grind)
            | exact superpose b5e75 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e75
               grind)
            | exact resolve b5e16 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e96 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e94 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e106 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e34 X0 X1 (M.op x x) X4
               have i₂ := b5e34 x X0 x X1
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ (M.op X0 (M.op (M.op X1 X2) X0)) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16 X3 (M.op (M.op X1 X2) X0)
               have i₂ := b5e34 X2 X0 X1 (M.op (M.op X1 X2) X0)
               grind)
            | exact superpose b5e34 b5e16
            | (have j0 := b5e16 X3 (M.op (M.op X1 X2) X0)
               grind)
            | exact resolve b5e16 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e120 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e113 X0 X1 X2 X3
               grind)
            | (have r₁ := b5e113 X1 X1 X2 X3
               have r₂ := b5e44 (M.op X1 X2) X1
               grind)
            | exact resolve b5e113 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e113
          have b5e122 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e120 X0 X1 X2 X3
               have i₂ := b5e34 X2 X0 X1 X3
               grind)
            | exact superpose b5e34 b5e120
            | exact resolve b5e120 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e120
          have b5e123 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op X2 X0)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e122 X0 x X2 X3
               have i₂ := b5e106 x X2 X0
               grind)
            | exact superpose b5e106 b5e122
            | exact resolve b5e122 b5e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106 b5e122
          have b5e473 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e63 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e475 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e473 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e473
          have b5e1139 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e475 x
               have i₂ := b5e96 x
               grind)
            | exact superpose b5e96 b5e475
            | (have j0 := b5e475 x
               grind)
            | exact resolve b5e475 b5e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e475
          have b5e1148 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1139
               have i₂ := b5e75
               grind)
            | exact superpose b5e75 b5e1139
            | exact resolve b5e1139 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75 b5e1139
          have b5e1149 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e1148
          have b5e1180 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e123 (σ x) (σ x) X0
               have i₂ := b5e1149
               grind)
            | exact superpose b5e1149 b5e123
            | exact resolve b5e123 b5e1149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123 b5e1149
          have b5e1249 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 x
               have i₂ := b5e1180 (σ X0)
               grind)
            | exact superpose b5e1180 b5e19
            | exact resolve b5e19 b5e1180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1180
          have b5e1261 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e1249 X0
               have i₂ := b5e96 X0
               grind)
            | exact superpose b5e96 b5e1249
            | exact resolve b5e1249 b5e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96 b5e1249
          have b5e1703 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1261 y
               grind)
            | exact superpose b5e1261 b5e20
            | (have r₁ := b5e20
               have r₂ := b5e1261 y
               grind)
            | exact resolve b5e20 b5e1261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1261
          have b5e1725 : False := by grind
          exact b5e1725
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e33 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b6e34 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e33 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e36 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e34 (σ X0)
             grind)
          | exact superpose b6e34 b6e18
          | exact resolve b6e18 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e81 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e36 y
             grind)
          | exact superpose b6e36 b6e22
          | exact resolve b6e22 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e118 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e81
             grind)
          | exact superpose b6e81 b6e13
          | exact resolve b6e13 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e120 : y = (k y y) := by
          first
          | (have i₁ := b6e118
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e118
          | exact resolve b6e118 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e118
        have b6e148 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e120
             grind)
          | exact superpose b6e120 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e149 : y = (M.op y y) := by grind
        clear b6e148
        have b6e153 : False := by grind
        exact b6e153
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X2 X0) X1) X3 X1
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e32 X0 X1 X2 X3
               have i₂ := b7e13 X1 X3 X0
               grind)
            | exact superpose b7e13 b7e32
            | exact resolve b7e32 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e51 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e53 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e51
          have b7e54 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e53
               have r₂ := b7e23
               grind)
            | exact resolve b7e53 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e55 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e54
            | exact resolve b7e54 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e59 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e14
            | exact resolve b7e14 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e60 : y = (k x y) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e59
            | exact resolve b7e59 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e79 : y = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e60
               grind)
            | exact superpose b7e60 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e80 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e79
               have r₂ := b7e21
               grind)
            | exact resolve b7e79 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e82 : y = (M.op y x) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e22
               grind)
            | exact resolve b7e80 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e102 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e34 X0 X1 (M.op x x) X4
               have i₂ := b7e34 x X0 x X1
               grind)
            | exact superpose b7e34 b7e34
            | exact resolve b7e34 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e107 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op x x)
               have i₂ := b7e34 x X0 x X1
               grind)
            | exact superpose b7e34 b7e13
            | exact resolve b7e13 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e158 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e102 y x X0
               have i₂ := b7e82
               grind)
            | exact superpose b7e82 b7e102
            | exact resolve b7e102 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e360 : y = (M.op x y) := by
            first
            | (have i₁ := b7e107 y x
               have i₂ := b7e82
               grind)
            | exact superpose b7e82 b7e107
            | exact resolve b7e107 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e107
          have b7e386 : y = (M.op y y) := by
            first
            | (have i₁ := b7e360
               have i₂ := b7e158 y
               grind)
            | exact superpose b7e158 b7e360
            | exact resolve b7e360 b7e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158 b7e360
          have b7e392 : False := by grind
          exact b7e392
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X2 X0) X1) X3 X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e31 X0 X1 X2 X3
               have i₂ := b8e13 X1 X3 X0
               grind)
            | exact superpose b8e13 b8e31
            | exact resolve b8e31 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e90 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e33 X0 X1 (M.op x x) X4
               have i₂ := b8e33 x X0 x X1
               grind)
            | exact superpose b8e33 b8e33
            | exact resolve b8e33 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 (M.op x x)
               have i₂ := b8e33 x X0 x X1
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ (M.op X0 (M.op (M.op X1 X2) X0)) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e16 X3 (M.op (M.op X1 X2) X0)
               have i₂ := b8e33 X2 X0 X1 (M.op (M.op X1 X2) X0)
               grind)
            | exact superpose b8e33 b8e16
            | (have j0 := b8e16 X3 (M.op (M.op X1 X2) X0)
               grind)
            | exact resolve b8e16 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e100 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op X1 X2) X0) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e99 X0 X1 X2 X3
               have i₂ := b8e13 X2 X0 X1
               grind)
            | exact superpose b8e13 b8e99
            | (have j0 := b8e99 X0 X1 X2 X3
               grind)
            | exact resolve b8e99 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e104 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b8e100 X0 X1 X2 X3
               grind)
            | (have r₁ := b8e100 x X0 X1 X3
               have r₂ := b8e90 X0 X1 x
               grind)
            | exact resolve b8e100 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e105 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e104 X0 X1 X2 X3
               have i₂ := b8e33 X2 X0 X1 X3
               grind)
            | exact superpose b8e33 b8e104
            | exact resolve b8e104 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e104
          have b8e106 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op X2 X0)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e105 X0 x X2 X3
               have i₂ := b8e90 x X2 X0
               grind)
            | exact superpose b8e90 b8e105
            | exact resolve b8e105 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e105
          have b8e179 : ∀ X0 X1 X2 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e39 X1 (M.op X2 X0)
               have i₂ := b8e106 X0 X2 (σ X1)
               grind)
            | exact superpose b8e106 b8e39
            | exact resolve b8e39 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e180 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = (k X1 (σ (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e25 X1 (M.op X2 X0)
               have i₂ := b8e106 X0 X2 (τ X1)
               grind)
            | exact superpose b8e106 b8e25
            | exact resolve b8e25 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e469 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (σ X0)
               have i₂ := b8e64 X0 X0
               grind)
            | exact superpose b8e64 b8e16
            | (have j0 := b8e16 X1 (σ X0)
               have j1 := b8e64 X0 X0
               grind)
            | (have r₁ := b8e16 X0 (σ X0)
               have r₂ := b8e64 X0 X1
               grind)
            | (have r₁ := b8e16 X0 (σ X1)
               have r₂ := b8e64 X1 X1
               grind)
            | exact resolve b8e16 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e487 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e469 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e469
          have b8e492 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e487 X0 X1
               have j1 := b8e16 X1 (σ X0)
               grind)
            | (have r₁ := b8e487 X0 X1
               have r₂ := b8e16 X0 (σ X0)
               grind)
            | exact resolve b8e487 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e487
          have b8e938 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) ≠ (σ (M.op X1 X0)) ∨ (k X2 (σ (M.op X1 X0))) = (M.op (σ (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e492 (M.op X1 X0) X2
               have i₂ := b8e106 X0 X1 (M.op X1 X0)
               grind)
            | exact superpose b8e106 b8e492
            | (have j0 := b8e492 (M.op X1 X0) X2
               grind)
            | exact resolve b8e492 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e492
          have b8e953 : ∀ X0 X1 X2 : G, (σ (M.op X1 X0)) ≠ (σ (M.op X1 X0)) ∨ (k X2 (σ (M.op X1 X0))) = (M.op (σ (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e938 X0 X1 X2
               have i₂ := b8e94 X1 X0
               grind)
            | exact superpose b8e94 b8e938
            | (have j0 := b8e938 X0 X1 X2
               grind)
            | exact resolve b8e938 b8e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94 b8e938
          have b8e954 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X1 X0))) = (M.op (σ (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e953 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e953
          have b8e962 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X0)) X2) = (σ (M.op X0 (τ X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e954 X0 X1 X2
               have i₂ := b8e180 X0 X2 X1
               grind)
            | exact superpose b8e180 b8e954
            | exact resolve b8e954 b8e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180 b8e954
          have b8e1179 : ∀ X0 X1 X2 : G, (τ (M.op X1 (σ X2))) = (k X2 (τ (σ (M.op X0 (τ X1))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e179 X1 X2 (σ (M.op x X0))
               have i₂ := b8e962 X0 x X1
               grind)
            | exact superpose b8e962 b8e179
            | exact resolve b8e179 b8e962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179 b8e962
          have b8e1199 : ∀ X0 X1 X2 : G, (τ (M.op X1 (σ X2))) = (k X2 (M.op X0 (τ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1179 X0 X1 X2
               have i₂ := b8e14 (M.op X0 (τ X1))
               grind)
            | exact superpose b8e14 b8e1179
            | exact resolve b8e1179 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1179
          have b8e1214 : ∀ X1 X2 : G, (M.op (τ X1) X2) = (τ (M.op X1 (σ X2))) := by
            intro X1 X2
            first
            | (have i₁ := b8e1199 x X1 X2
               have i₂ := b8e106 (τ X1) x X2
               grind)
            | exact superpose b8e106 b8e1199
            | exact resolve b8e1199 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1199
          have b8e1521 : ∀ X0 X1 X2 : G, (k (σ X2) (M.op X0 (σ X1))) = (σ (k X2 (M.op (τ X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e26 (M.op X0 (σ X1)) X2
               have i₂ := b8e1214 X0 X1
               grind)
            | exact superpose b8e1214 b8e26
            | exact resolve b8e26 b8e1214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e1214
          have b8e1530 : ∀ X0 X1 X2 : G, (σ (M.op X1 X2)) = (k (σ X2) (M.op X0 (σ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1521 X0 X1 X2
               have i₂ := b8e106 X1 (τ X0) X2
               grind)
            | exact superpose b8e106 b8e1521
            | exact resolve b8e1521 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1521
          have b8e1538 : ∀ X1 X2 : G, (σ (M.op X1 X2)) = (M.op (σ X1) (σ X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e1530 x X1 X2
               have i₂ := b8e106 (σ X1) x (σ X2)
               grind)
            | exact superpose b8e106 b8e1530
            | exact resolve b8e1530 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106 b8e1530
          have b8e2461 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1538 x y
               grind)
            | exact superpose b8e1538 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e1538 x y
               grind)
            | exact resolve b8e20 b8e1538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1538
          have b8e2491 : False := by grind
          exact b8e2491

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_y_x_pyx_Equation3583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y x) := by grind
        have b0e22 : (k x y) = (M.op x (k x y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : x ≠ x ∨ y = (k x y) := by
          first
          | (have i₁ := b0e15 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 x y
             grind)
          | (have r₁ := b0e15 x y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e29 : y = (k x y) := by grind
        clear b0e24
        have b0e31 : y = (M.op x y) := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e29
             grind)
          | exact superpose b0e29 b0e22
          | exact resolve b0e22 b0e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e29
        have b0e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X2 (M.op (M.op X0 X0) X1) X3
             have i₂ := b0e12 X0 X1 (M.op X2 X2)
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e37 X0 X1 x X3
             have i₂ := b0e12 X0 X1 x
             grind)
          | exact superpose b0e12 b0e37
          | exact resolve b0e37 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37
        have b0e46 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e39 x y x
             have i₂ := b0e31
             grind)
          | exact superpose b0e31 b0e39
          | exact resolve b0e39 b0e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1 x
             have i₂ := b0e39 (M.op X0 X0) X1 x
             grind)
          | exact superpose b0e39 b0e12
          | exact resolve b0e12 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e96 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e15 y X0
             have i₂ := b0e46 X0
             grind)
          | exact superpose b0e46 b0e15
          | (have j0 := b0e15 y X0
             grind)
          | (have r₁ := b0e15 y X0
             have r₂ := b0e46 X0
             grind)
          | exact resolve b0e15 b0e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e46
        have b0e98 : ∀ X0 : G, (k y X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e96 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e96
        have b0e242 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e33 X0 y
             have i₂ := b0e98 (τ X0)
             grind)
          | exact superpose b0e98 b0e33
          | exact resolve b0e33 b0e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33 b0e98
        have b0e243 : ∀ X0 : G, (k (σ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e242 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e242
          | exact resolve b0e242 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e242
        have b0e296 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear b0e243
        have b0e301 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e296
             have i₂ := b0e49 (σ y) (σ y)
             grind)
          | exact superpose b0e49 b0e296
          | exact resolve b0e296 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e49 b0e296
        have b0e302 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b0e301
        have b0e1444 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e39 (σ y) (σ y) x
             have i₂ := b0e302
             grind)
          | exact superpose b0e302 b0e39
          | exact resolve b0e39 b0e302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39 b0e302
        have b0e1587 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e1444 (σ x)
             grind)
          | exact superpose b0e1444 b0e19
          | exact resolve b0e19 b0e1444
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1444
        have b0e1591 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e1587
             have i₂ := b0e31
             grind)
          | exact superpose b0e31 b0e1587
          | exact resolve b0e1587 b0e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e31 b0e1587
        have b0e1592 : False := by grind
        exact b0e1592
      · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : x = (M.op y x) := by grind
          have b1e23 : (k x y) ≠ (M.op x (k x y)) := by grind
          have b1e24 : x = (M.op (k x y) (k x y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : x ≠ x ∨ y = (k x y) := by
            first
            | (have i₁ := b1e16 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e16
            | (have j0 := b1e16 x y
               grind)
            | (have r₁ := b1e16 x y
               have r₂ := b1e21
               grind)
            | exact resolve b1e16 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e30 : y = (k x y) := by grind
          clear b1e26
          have b1e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b1e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 (τ X0)
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e34 : x = (M.op y y) := by
            first
            | (have i₁ := b1e24
               have i₂ := b1e30
               grind)
            | exact superpose b1e30 b1e24
            | exact resolve b1e24 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : y ≠ (M.op x y) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e30
               grind)
            | exact superpose b1e30 b1e23
            | exact resolve b1e23 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 (M.op (M.op X0 X0) X1) X2 X3
               have i₂ := b1e13 X0 X1 (M.op (M.op X0 X0) X1)
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e39 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 y X0 X1
               have i₂ := b1e34
               grind)
            | exact superpose b1e34 b1e13
            | exact resolve b1e13 b1e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X0 X0) X1) X3
               have i₂ := b1e13 X0 X1 (M.op X2 X2)
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e40 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e40
            | exact resolve b1e40 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e40
          have b1e46 : y = (k y x) ∨ y = (M.op x y) := by grind
          have b1e47 : y = (k y x) := by
            first
            | (have r₁ := b1e46
               have r₂ := b1e35
               grind)
            | exact resolve b1e46 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e46
          have b1e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 X0
               have i₂ := b1e18 (σ X1) (σ X0)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X0)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e63 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X3 (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X1 X2 X3
               have i₂ := b1e18 X1 X0
               grind)
            | (have i₁ := b1e13 X0 X1 X2
               have i₂ := b1e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b1e18 b1e13
            | (have j1 := b1e18 X1 X0
               grind)
            | exact resolve b1e13 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e66 : ∀ X0 : G, x = X0 ∨ (M.op X0 (k x y)) = (k (k x y) X0) ∨ (k x y) = (M.op X0 (k x y)) := by
            intro X0
            first
            | (have i₁ := b1e24
               have i₂ := b1e18 (k x y) X0
               grind)
            | (have i₁ := b1e24
               have i₂ := b1e18 X0 (M.op (k x y) (k x y))
               grind)
            | exact superpose b1e18 b1e24
            | (have j1 := b1e18 (k x y) X0
               grind)
            | exact resolve b1e24 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e70 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
            intro X0
            first
            | (have i₁ := b1e66 X0
               have i₂ := b1e30
               grind)
            | exact superpose b1e30 b1e66
            | (have j0 := b1e66 X0
               grind)
            | exact resolve b1e66 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e66
          have b1e71 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e63 X0 X1 X2 x
               have i₂ := b1e42 X0 X2 x
               grind)
            | exact superpose b1e42 b1e63
            | (have j0 := b1e63 X0 X1 X2 x
               grind)
            | exact resolve b1e63 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e63
          have b1e73 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 y) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b1e70 X0
               have i₂ := b1e30
               grind)
            | exact superpose b1e30 b1e70
            | (have j0 := b1e70 X0
               grind)
            | exact resolve b1e70 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e30 b1e70
          have b1e81 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b1e42 y y x
               have i₂ := b1e34
               grind)
            | exact superpose b1e34 b1e42
            | exact resolve b1e42 b1e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e84 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 X1 x
               have i₂ := b1e42 (M.op X0 X0) X1 x
               grind)
            | exact superpose b1e42 b1e13
            | exact resolve b1e13 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e85 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e16 (M.op X0 X1) X2
               have i₂ := b1e42 X0 X1 X2
               grind)
            | exact superpose b1e42 b1e16
            | (have j0 := b1e16 (M.op X0 X1) X2
               grind)
            | (have r₁ := b1e16 (M.op X0 X1) x
               have r₂ := b1e42 X0 X1 x
               grind)
            | exact resolve b1e16 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e90 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b1e85 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e85
          have b1e100 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            grind
          have b1e104 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b1e14 (k (τ X0) X1)
               have i₂ := b1e32 X0 X1
               grind)
            | exact superpose b1e32 b1e14
            | exact resolve b1e14 b1e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32
          have b1e105 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e100 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e100
            | (have j0 := b1e100 X0
               grind)
            | exact resolve b1e100 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e100
          have b1e106 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e105 X0
               have i₂ := b1e84 (τ X0) (τ X0)
               grind)
            | exact superpose b1e84 b1e105
            | (have j0 := b1e105 X0
               grind)
            | exact resolve b1e105 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e105
          have b1e114 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e33 X0 X1
               have i₂ := b1e18 X1 (τ X0)
               grind)
            | exact superpose b1e18 b1e33
            | (have j1 := b1e18 X1 (τ X0)
               grind)
            | exact resolve b1e33 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e156 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) x) X1) = (M.op X2 (M.op x X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e37 X0 x X1 X2
               have i₂ := b1e81 X0
               grind)
            | exact superpose b1e81 b1e37
            | exact resolve b1e37 b1e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e37
          have b1e210 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op X0 X0) x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e156 X0 X1 x
               have i₂ := b1e39 X1 x
               grind)
            | exact superpose b1e39 b1e156
            | exact resolve b1e156 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e39 b1e156
          have b1e238 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b1e210 x X1
               have i₂ := b1e81 (M.op x x)
               grind)
            | exact superpose b1e81 b1e210
            | exact resolve b1e210 b1e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e81 b1e210
          have b1e299 : x = (M.op x y) := by
            first
            | (have i₁ := b1e34
               have i₂ := b1e238 y
               grind)
            | exact superpose b1e238 b1e34
            | exact resolve b1e34 b1e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e238
          have b1e339 : x ≠ y := by
            first
            | (have i₁ := b1e35
               have i₂ := b1e299
               grind)
            | exact superpose b1e299 b1e35
            | exact resolve b1e35 b1e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e438 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e20
               have i₂ := b1e71 (σ x) X0 (σ y)
               grind)
            | (have i₁ := b1e20
               have i₂ := b1e71 X0 (σ x) (σ y)
               grind)
            | exact superpose b1e71 b1e20
            | (have j1 := b1e71 (σ x) X0 x
               grind)
            | exact resolve b1e20 b1e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e454 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b1e71 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e71
          have b1e462 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e438 X0
               have i₂ := b1e299
               grind)
            | exact superpose b1e299 b1e438
            | (have j0 := b1e438 X0
               grind)
            | exact resolve b1e438 b1e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e299 b1e438
          have b1e583 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e18 (σ X0) X1
               have i₂ := b1e56 X0 X0
               grind)
            | exact superpose b1e56 b1e18
            | (have j0 := b1e18 (σ X0) X1
               have j1 := b1e56 X0 X0
               grind)
            | exact resolve b1e18 b1e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e56
          have b1e619 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b1e583 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e583
          have b1e637 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X0)) = X1 ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b1e619 X0 X1
               have j1 := b1e454 X1 (σ X0)
               grind)
            | (have r₁ := b1e619 X0 (M.op (σ (k X0 X0)) (σ (k X0 X0)))
               have r₂ := b1e454 X0 (σ (k X0 X0))
               grind)
            | (have r₁ := b1e619 X0 (σ X0)
               have r₂ := b1e454 X0 (σ X0)
               grind)
            | (have r₁ := b1e619 X0 X1
               have r₂ := b1e454 X0 (σ X0)
               grind)
            | exact resolve b1e619 b1e454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e619
          have b1e806 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e104 X2 (k X0 (τ X1))
               have i₂ := b1e33 X1 X0
               grind)
            | exact superpose b1e33 b1e104
            | exact resolve b1e104 b1e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e33
          have b1e813 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e104 (M.op X1 X2) X0
               have i₂ := b1e90 X1 X2 (σ X0)
               grind)
            | exact superpose b1e90 b1e104
            | exact resolve b1e104 b1e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e90 b1e104
          have b1e830 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e813 X0 X1 X2
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e813
            | exact resolve b1e813 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e813
          have b1e3123 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e106 X0
               have i₂ := b1e114 X0 (τ X0)
               grind)
            | exact superpose b1e114 b1e106
            | (have j0 := b1e106 X0
               have j1 := b1e114 X0 (τ X0)
               grind)
            | exact resolve b1e106 b1e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e106 b1e114
          have b1e3215 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b1e3123 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3123
          have b1e3243 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e3215 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e3215
            | (have j0 := b1e3215 X0
               grind)
            | exact resolve b1e3215 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3215
          have b1e3955 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) := by
            intro X0
            grind
          have b1e3985 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have j0 := b1e3955 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3955
          have b1e3997 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e3985 X0
               have i₂ := b1e84 (σ X0) (σ X0)
               grind)
            | exact superpose b1e84 b1e3985
            | (have j0 := b1e3985 X0
               grind)
            | exact resolve b1e3985 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e84 b1e3985
          have b1e28542 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b1e806 X0 (σ X0) (σ X0)
               have i₂ := b1e3243 (σ X0)
               grind)
            | exact superpose b1e3243 b1e806
            | (have j1 := b1e3243 (σ X0)
               grind)
            | exact resolve b1e806 b1e3243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e806 b1e3243
          have b1e28688 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b1e28542 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e28542
            | (have j0 := b1e28542 X0
               grind)
            | exact resolve b1e28542 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e28542
          have b1e28722 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e28688 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e28688
            | (have j0 := b1e28688 X0
               grind)
            | exact resolve b1e28688 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e28688
          have b1e30717 : y = (M.op (k y y) y) ∨ y = (M.op (k y y) y) ∨ x = (k y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b1e73 (k y y)
               have i₂ := b1e28722 y
               grind)
            | exact superpose b1e28722 b1e73
            | (have j0 := b1e73 (k y y)
               have j1 := b1e28722 y
               grind)
            | exact resolve b1e73 b1e28722
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e73 b1e28722
          have b1e30718 : y = (M.op (k y y) y) ∨ x = (k y y) ∨ y = (M.op y y) := by grind
          clear b1e30717
          have b1e30784 : x = y ∨ y = (M.op (k y y) y) ∨ x = (k y y) := by
            first
            | (have i₁ := b1e30718
               have i₂ := b1e34
               grind)
            | exact superpose b1e34 b1e30718
            | exact resolve b1e30718 b1e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e34 b1e30718
          have b1e30835 : y = (M.op (k y y) y) ∨ x = (k y y) := by
            first
            | (have r₁ := b1e30784
               have r₂ := b1e339
               grind)
            | exact resolve b1e30784 b1e339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e30784
          have b1e32054 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k y y) := by
            intro X0
            first
            | (have i₁ := b1e42 (k y y) y x
               have i₂ := b1e30835
               grind)
            | exact superpose b1e30835 b1e42
            | exact resolve b1e42 b1e30835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42 b1e30835
          have b1e33975 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (k y y) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 y X1
               have i₂ := b1e32054 (M.op X0 X0)
               grind)
            | exact superpose b1e32054 b1e13
            | exact resolve b1e13 b1e32054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e41472 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ x = (k y y) := by
            intro X0
            first
            | (have i₁ := b1e35
               have i₂ := b1e33975 x X0
               grind)
            | (have i₁ := b1e35
               have i₂ := b1e33975 X0 x
               grind)
            | exact superpose b1e33975 b1e35
            | exact resolve b1e35 b1e33975
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35 b1e33975
          have b1e41535 : x = (k y y) := by
            first
            | (have r₁ := b1e41472 x
               have r₂ := b1e32054 x
               grind)
            | exact resolve b1e41472 b1e32054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32054 b1e41472
          have b1e41687 : (σ x) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e462 (σ y)
               have i₂ := b1e3997 y
               grind)
            | exact superpose b1e3997 b1e462
            | (have j0 := b1e462 (σ y)
               have j1 := b1e3997 y
               grind)
            | exact resolve b1e462 b1e3997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e462 b1e3997
          have b1e41785 : (σ x) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j1 := b1e454 (σ x) (σ y)
               grind)
            | (have r₁ := b1e41687
               have r₂ := b1e454 x (σ y)
               grind)
            | exact resolve b1e41687 b1e454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e454 b1e41687
          have b1e41801 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j1 := b1e637 y (σ x)
               grind)
            | (have r₁ := b1e41785
               have r₂ := b1e637 y (σ x)
               grind)
            | exact resolve b1e41785 b1e637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e637 b1e41785
          have b1e41806 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e41801
               have i₂ := b1e19 y x
               grind)
            | exact superpose b1e19 b1e41801
            | exact resolve b1e41801 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41801
          have b1e41807 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e41806
               have i₂ := b1e47
               grind)
            | exact superpose b1e47 b1e41806
            | exact resolve b1e41806 b1e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47 b1e41806
          have b1e41808 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b1e41807
          have b1e42089 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e830 X0 (σ x) (σ y)
               have i₂ := b1e41808
               grind)
            | exact superpose b1e41808 b1e830
            | exact resolve b1e830 b1e41808
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e830 b1e41808
          have b1e42120 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e42089 X0
               have i₂ := b1e14 y
               grind)
            | exact superpose b1e14 b1e42089
            | exact resolve b1e42089 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42089
          have b1e42494 : x = y := by
            first
            | (have i₁ := b1e41535
               have i₂ := b1e42120 y
               grind)
            | exact superpose b1e42120 b1e41535
            | exact resolve b1e41535 b1e42120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41535 b1e42120
          have b1e42590 : False := by grind
          exact b1e42590
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = (M.op y x) := by grind
          have b2e23 : (k x y) ≠ (M.op x (k x y)) := by grind
          have b2e24 : x ≠ (M.op (k x y) (k x y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : x ≠ x ∨ y = (k x y) := by
            first
            | (have i₁ := b2e16 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 x y
               grind)
            | (have r₁ := b2e16 x y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e29 : y = (k x y) := by grind
          clear b2e26
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
          have b2e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e34 : y ≠ (M.op x y) := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e29
               grind)
            | exact superpose b2e29 b2e23
            | exact resolve b2e23 b2e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X0 X0) X1) X3
               have i₂ := b2e13 X0 X1 (M.op X2 X2)
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e36 X0 X1 x X3
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e36
            | exact resolve b2e36 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36
          have b2e45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 X1 x
               have i₂ := b2e38 (M.op X0 X0) X1 x
               grind)
            | exact superpose b2e38 b2e13
            | exact resolve b2e13 b2e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e46 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e16 (M.op X0 X1) X2
               have i₂ := b2e38 X0 X1 X2
               grind)
            | exact superpose b2e38 b2e16
            | (have j0 := b2e16 (M.op X0 X1) X2
               grind)
            | (have r₁ := b2e16 (M.op X0 X1) x
               have r₂ := b2e38 X0 X1 x
               grind)
            | exact resolve b2e16 b2e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e50 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e46 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46
          have b2e63 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e68 : ∀ X0 : G, x ≠ X0 ∨ (M.op X0 (k x y)) = (k (k x y) X0) ∨ (k x y) = (M.op X0 (k x y)) := by
            intro X0
            first
            | (have i₁ := b2e24
               have i₂ := b2e18 (k x y) X0
               grind)
            | (have i₁ := b2e24
               have i₂ := b2e18 X0 (M.op (k x y) (k x y))
               grind)
            | exact superpose b2e18 b2e24
            | (have j1 := b2e18 (k x y) X0
               grind)
            | (have r₁ := b2e24
               have r₂ := b2e18 (k x y) x
               grind)
            | exact resolve b2e24 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63
          have b2e70 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x ≠ X0 ∨ (k x y) = (M.op X0 (k x y)) := by
            intro X0
            first
            | (have i₁ := b2e68 X0
               have i₂ := b2e29
               grind)
            | exact superpose b2e29 b2e68
            | (have j0 := b2e68 X0
               grind)
            | exact resolve b2e68 b2e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e68
          have b2e72 : ∀ X0 : G, x ≠ X0 ∨ (M.op X0 y) = (k y X0) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e70 X0
               have i₂ := b2e29
               grind)
            | exact superpose b2e29 b2e70
            | (have j0 := b2e70 X0
               grind)
            | exact resolve b2e70 b2e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e29 b2e70
          have b2e81 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            grind
          have b2e85 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b2e31
          have b2e86 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b2e81 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e81
            | (have j0 := b2e81 X0
               grind)
            | exact resolve b2e81 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e81
          have b2e87 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b2e86 X0
               have i₂ := b2e45 (τ X0) (τ X0)
               grind)
            | exact superpose b2e45 b2e86
            | (have j0 := b2e86 X0
               grind)
            | exact resolve b2e86 b2e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45 b2e86
          have b2e101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e32 X1 X0
               grind)
            | exact superpose b2e32 b2e14
            | exact resolve b2e14 b2e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32
          have b2e237 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
            first
            | (have j0 := b2e72 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e72
          have b2e238 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b2e237
               have r₂ := b2e34
               grind)
            | exact resolve b2e237 b2e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e237
          have b2e255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e69 (σ X1) (σ X0)
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e69
            | (have j0 := b2e69 (σ X1) (σ X0)
               grind)
            | exact resolve b2e69 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e69
          have b2e732 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e85 (M.op X1 X2) X0
               have i₂ := b2e50 X1 X2 (σ X0)
               grind)
            | exact superpose b2e50 b2e85
            | exact resolve b2e85 b2e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e50 b2e85
          have b2e750 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e732 X0 X1 X2
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e732
            | exact resolve b2e732 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e732
          have b2e1762 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b2e101 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
               have i₂ := b2e87 (σ X0)
               grind)
            | exact superpose b2e87 b2e101
            | (have j1 := b2e87 (σ X0)
               grind)
            | exact resolve b2e101 b2e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e87 b2e101
          have b2e1794 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b2e1762 X0
               have i₂ := b2e14 (M.op (τ (σ X0)) (τ (σ X0)))
               grind)
            | exact superpose b2e14 b2e1762
            | (have j0 := b2e1762 X0
               grind)
            | exact resolve b2e1762 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1762
          have b2e1817 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b2e1794 X0
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e1794
            | (have j0 := b2e1794 X0
               grind)
            | exact resolve b2e1794 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1794
          have b2e1824 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e1817 X0
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e1817
            | (have j0 := b2e1817 X0
               grind)
            | exact resolve b2e1817 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1817
          have b2e5446 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e255 y x
               grind)
            | exact superpose b2e255 b2e20
            | (have j1 := b2e255 y x
               grind)
            | exact resolve b2e20 b2e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e255
          have b2e5514 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e5446
               have i₂ := b2e238
               grind)
            | exact superpose b2e238 b2e5446
            | exact resolve b2e5446 b2e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5446
          have b2e5515 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
          clear b2e5514
          have b2e5529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b2e5515
               have i₂ := b2e238
               grind)
            | exact superpose b2e238 b2e5515
            | exact resolve b2e5515 b2e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238 b2e5515
          have b2e25049 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e750 X0 (σ x) (σ y)
               have i₂ := b2e5529
               grind)
            | exact superpose b2e5529 b2e750
            | exact resolve b2e750 b2e5529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e750 b2e5529
          have b2e25079 : ∀ X0 : G, (k y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e25049 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e25049
            | exact resolve b2e25049 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e25049
          have b2e26273 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e25079 X0
               grind)
            | exact superpose b2e25079 b2e14
            | (have j1 := b2e25079 X0
               grind)
            | exact resolve b2e14 b2e25079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e25079
          have b2e26391 : ∀ X0 : G, y = (M.op x y) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e26273 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e26273
            | (have j0 := b2e26273 X0
               grind)
            | exact resolve b2e26273 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26273
          have b2e26413 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e26391 X0
               grind)
            | (have r₁ := b2e26391 X0
               have r₂ := b2e34
               grind)
            | exact resolve b2e26391 b2e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26391
          have b2e27914 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b2e1824 y
               have i₂ := b2e26413 (M.op y y)
               grind)
            | exact superpose b2e26413 b2e1824
            | (have j0 := b2e1824 y
               grind)
            | exact resolve b2e1824 b2e26413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1824 b2e26413
          have b2e27939 : y = (M.op y y) := by grind
          clear b2e27914
          have b2e32737 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e38 y y x
               have i₂ := b2e27939
               grind)
            | exact superpose b2e27939 b2e38
            | exact resolve b2e38 b2e27939
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e38 b2e27939
          have b2e34048 : y ≠ y := by
            first
            | (have i₁ := b2e34
               have i₂ := b2e32737 x
               grind)
            | exact superpose b2e32737 b2e34
            | (have r₁ := b2e34
               have r₂ := b2e32737 x
               grind)
            | exact resolve b2e34 b2e32737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e34 b2e32737
          have b2e34050 : False := by grind
          exact b2e34050
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : x = (M.op y x) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : x ≠ x ∨ y = (k x y) := by
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
          have b3e30 : y = (k x y) := by grind
          clear b3e26
          have b3e43 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          have b3e44 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e43
               have r₂ := b3e22
               grind)
            | exact resolve b3e43 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e43
          have b3e45 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e44
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e44
            | exact resolve b3e44 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e44
          have b3e46 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e45
               have i₂ := b3e30
               grind)
            | exact superpose b3e30 b3e45
            | exact resolve b3e45 b3e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e30 b3e45
          have b3e48 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e46
               grind)
            | exact superpose b3e46 b3e22
            | exact resolve b3e22 b3e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e55 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e48
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e48
            | exact resolve b3e48 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e48
          have b3e57 : False := by grind
          exact b3e57
        · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : x ≠ x ∨ y = (k x y) := by
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
            have b4e31 : y = (k x y) := by grind
            clear b4e28
            have b4e47 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b4e52 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e47
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e47 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e47
            have b4e54 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b4e52
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e52
              | exact resolve b4e52 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e52
            have b4e55 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e54
                 have i₂ := b4e31
                 grind)
              | exact superpose b4e31 b4e54
              | exact resolve b4e54 b4e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e31 b4e54
            have b4e57 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e55
                 grind)
              | exact superpose b4e55 b4e23
              | exact resolve b4e23 b4e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e64 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e57
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e57
              | exact resolve b4e57 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e57
            have b4e66 : False := by grind
            exact b4e66
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : x = (M.op y x) := by grind
            have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : x ≠ x ∨ y = (k x y) := by
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
            have b5e30 : y = (k x y) := by grind
            clear b5e28
            have b5e52 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b5e55 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e52
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e52 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e52
            have b5e56 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e55
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e55
              | exact resolve b5e55 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e55
            have b5e57 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e56
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e56
              | exact resolve b5e56 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e56
            have b5e59 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e57
                 grind)
              | exact superpose b5e57 b5e23
              | exact resolve b5e23 b5e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e66 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e59
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e59
              | exact resolve b5e59 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e59
            have b5e68 : False := by grind
            exact b5e68
      · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
          have b6e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : (k x y) = (M.op x (k x y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : x ≠ x ∨ y = (k x y) := by
            first
            | (have i₁ := b6e16 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 x y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e29 : y = (k x y) := by grind
          clear b6e26
          have b6e32 : y = (M.op x y) := by
            first
            | (have i₁ := b6e24
               have i₂ := b6e29
               grind)
            | exact superpose b6e29 b6e24
            | exact resolve b6e24 b6e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X2 (M.op (M.op X0 X0) X1) X3
               have i₂ := b6e13 X0 X1 (M.op X2 X2)
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e36 X0 X1 x X3
               have i₂ := b6e13 X0 X1 x
               grind)
            | exact superpose b6e13 b6e36
            | exact resolve b6e36 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e36
          have b6e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e23
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e443 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b6e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e56
          have b6e444 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e443
               have r₂ := b6e22
               grind)
            | exact resolve b6e443 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e443
          have b6e445 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e444
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e444
            | exact resolve b6e444 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e444
          have b6e446 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b6e445
               have i₂ := b6e29
               grind)
            | exact superpose b6e29 b6e445
            | exact resolve b6e445 b6e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e29 b6e445
          have b6e669 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e38 (σ y) (σ x) x
               have i₂ := b6e446
               grind)
            | exact superpose b6e446 b6e38
            | exact resolve b6e38 b6e446
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38 b6e446
          have b6e892 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e669 (σ x)
               grind)
            | exact superpose b6e669 b6e20
            | exact resolve b6e20 b6e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e669
          have b6e896 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e892
               have i₂ := b6e32
               grind)
            | exact superpose b6e32 b6e892
            | exact resolve b6e892 b6e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32 b6e892
          have b6e897 : False := by grind
          exact b6e897
        · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b7e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : x = (M.op y x) := by grind
            have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e25 : (k x y) ≠ (M.op x (k x y)) := by grind
            have b7e26 : x = (M.op (k x y) (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : x ≠ x ∨ y = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 x y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e30 : y = (k x y) := by grind
            clear b7e28
            have b7e31 : x = (M.op y y) := by
              first
              | (have i₁ := b7e26
                 have i₂ := b7e30
                 grind)
              | exact superpose b7e30 b7e26
              | exact resolve b7e26 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e32 : y ≠ (M.op x y) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e30
                 grind)
              | exact superpose b7e30 b7e25
              | exact resolve b7e25 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 (τ X0) X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e36 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 y X0 X1
                 have i₂ := b7e31
                 grind)
              | exact superpose b7e31 b7e14
              | exact resolve b7e14 b7e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 (M.op (M.op X0 X0) X1) X2 X3
                 have i₂ := b7e14 X0 X1 (M.op (M.op X0 X0) X1)
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X2 (M.op (M.op X0 X0) X1) X3
                 have i₂ := b7e14 X0 X1 (M.op X2 X2)
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e41 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b7e39 X0 X1 x X3
                 have i₂ := b7e14 X0 X1 x
                 grind)
              | exact superpose b7e14 b7e39
              | exact resolve b7e39 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e39
            have b7e43 : y = (k y x) ∨ y = (M.op x y) := by grind
            have b7e47 : y = (k y x) := by
              first
              | (have r₁ := b7e43
                 have r₂ := b7e32
                 grind)
              | exact resolve b7e43 b7e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e43
            have b7e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e24
                 have i₂ := b7e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b7e19 b7e24
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e24
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e24 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e77 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b7e41 (k x y) (k x y) x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e41
              | exact resolve b7e41 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e84 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e17 (M.op X0 X1) X2
                 have i₂ := b7e41 X0 X1 X2
                 grind)
              | exact superpose b7e41 b7e17
              | (have j0 := b7e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b7e17 (M.op X0 X1) x
                 have r₂ := b7e41 X0 X1 x
                 grind)
              | exact resolve b7e17 b7e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e41
            have b7e89 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b7e84 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e84
            have b7e96 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b7e15 (k (τ X0) X1)
                 have i₂ := b7e33 X0 X1
                 grind)
              | exact superpose b7e33 b7e15
              | exact resolve b7e15 b7e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e33
            have b7e147 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) x) X1) = (M.op X2 (M.op x X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e38 X0 x X1 X2
                 have i₂ := b7e77 X0
                 grind)
              | exact superpose b7e77 b7e38
              | exact resolve b7e38 b7e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e199 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op X0 X0) x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e147 X0 X1 x
                 have i₂ := b7e36 X1 x
                 grind)
              | exact superpose b7e36 b7e147
              | exact resolve b7e147 b7e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e147
            have b7e227 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
              intro X1
              first
              | (have i₁ := b7e199 x X1
                 have i₂ := b7e77 (M.op x x)
                 grind)
              | exact superpose b7e77 b7e199
              | exact resolve b7e199 b7e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e77 b7e199
            have b7e277 : x = (M.op x y) := by
              first
              | (have i₁ := b7e31
                 have i₂ := b7e227 y
                 grind)
              | exact superpose b7e227 b7e31
              | exact resolve b7e31 b7e227
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31 b7e227
            have b7e317 : x ≠ y := by
              first
              | (have i₁ := b7e32
                 have i₂ := b7e277
                 grind)
              | exact superpose b7e277 b7e32
              | exact resolve b7e32 b7e277
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e32 b7e277
            have b7e525 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e65 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e65
            have b7e526 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e525
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e525 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e525
            have b7e527 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e526
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e526
              | exact resolve b7e526 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e526
            have b7e528 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e527
                 have i₂ := b7e30
                 grind)
              | exact superpose b7e30 b7e527
              | exact resolve b7e527 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e30 b7e527
            have b7e537 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e89 (σ y) (σ x) X0
                 have i₂ := b7e528
                 grind)
              | exact superpose b7e528 b7e89
              | exact resolve b7e89 b7e528
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e89 b7e528
            have b7e843 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b7e96 (σ y) X0
                 have i₂ := b7e537 (σ X0)
                 grind)
              | exact superpose b7e537 b7e96
              | exact resolve b7e96 b7e537
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e96 b7e537
            have b7e852 : ∀ X0 : G, (τ (σ X0)) = (k y X0) := by
              intro X0
              first
              | (have i₁ := b7e843 X0
                 have i₂ := b7e15 y
                 grind)
              | exact superpose b7e15 b7e843
              | exact resolve b7e843 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e843
            have b7e858 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e852 X0
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e852
              | exact resolve b7e852 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e852
            have b7e869 : x = y := by
              first
              | (have i₁ := b7e47
                 have i₂ := b7e858 x
                 grind)
              | exact superpose b7e858 b7e47
              | exact resolve b7e47 b7e858
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e47 b7e858
            have b7e886 : False := by grind
            exact b7e886
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : x = (M.op y x) := by grind
            have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X2 (M.op (M.op X0 X0) X1) X3
                 have i₂ := b8e14 X0 X1 (M.op X2 X2)
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e35 X0 X1 x X3
                 have i₂ := b8e14 X0 X1 x
                 grind)
              | exact superpose b8e14 b8e35
              | exact resolve b8e35 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35
            have b8e38 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e37 y x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e37
              | exact resolve b8e37 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 X1 x
                 have i₂ := b8e37 (M.op X0 X0) X1 x
                 grind)
              | exact superpose b8e37 b8e14
              | exact resolve b8e14 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e53 : ∀ X0 : G, x ≠ x ∨ (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e17 x X0
                 have i₂ := b8e38 X0
                 grind)
              | exact superpose b8e38 b8e17
              | (have j0 := b8e17 x X0
                 grind)
              | (have r₁ := b8e17 x X0
                 have r₂ := b8e38 X0
                 grind)
              | exact resolve b8e17 b8e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e38
            have b8e55 : ∀ X0 : G, (k x X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e53 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e53
            have b8e105 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b8e33 X0 x
                 have i₂ := b8e55 (τ X0)
                 grind)
              | exact superpose b8e55 b8e33
              | exact resolve b8e33 b8e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33 b8e55
            have b8e113 : ∀ X0 : G, (k (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e105 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e105
              | exact resolve b8e105 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e105
            have b8e119 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
            clear b8e113
            have b8e123 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b8e119
                 have i₂ := b8e42 (σ x) (σ x)
                 grind)
              | exact superpose b8e42 b8e119
              | exact resolve b8e119 b8e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e42 b8e119
            have b8e124 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b8e123
            have b8e313 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b8e37 (σ x) (σ x) x
                 have i₂ := b8e124
                 grind)
              | exact superpose b8e124 b8e37
              | exact resolve b8e37 b8e124
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37 b8e124
            have b8e461 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e313 (σ y)
                 grind)
              | exact superpose b8e313 b8e23
              | (have r₁ := b8e23
                 have r₂ := b8e313 (σ y)
                 grind)
              | exact resolve b8e23 b8e313
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e313
            have b8e463 : False := by grind
            exact b8e463
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : x ≠ (M.op y x) := by grind
          have b9e22 : y = (M.op x x) := by grind
          have b9e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b9e24 : (k x y) = (M.op x (k x y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e28 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ y)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e29 : (σ y) = (k (σ x) (σ y)) := by grind
          clear b9e28
          have b9e31 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e29
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e29
            | exact resolve b9e29 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e29
          have b9e36 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e31
               grind)
            | exact superpose b9e31 b9e14
            | exact resolve b9e14 b9e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e31
          have b9e37 : y = (k x y) := by
            first
            | (have i₁ := b9e36
               have i₂ := b9e14 y
               grind)
            | exact superpose b9e14 b9e36
            | exact resolve b9e36 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e36
          have b9e47 : x = (k x y) ∨ x = (M.op y x) := by grind
          have b9e49 : x = (k x y) := by
            first
            | (have r₁ := b9e47
               have r₂ := b9e21
               grind)
            | exact resolve b9e47 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e47
          have b9e51 : x = y := by
            first
            | (have i₁ := b9e37
               have i₂ := b9e49
               grind)
            | exact superpose b9e49 b9e37
            | exact resolve b9e37 b9e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e54 : x = (M.op x x) := by
            first
            | (have i₁ := b9e24
               have i₂ := b9e49
               grind)
            | exact superpose b9e49 b9e24
            | exact resolve b9e24 b9e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e49
          have b9e76 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e51
               grind)
            | exact superpose b9e51 b9e21
            | exact resolve b9e21 b9e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e51
          have b9e85 : False := by grind
          exact b9e85
        · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : x ≠ (M.op y x) := by grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : (k x y) ≠ (M.op x (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b10e29
            have b10e32 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b10e31
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e31
              | exact resolve b10e31 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e31
            have b10e33 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e32
                 grind)
              | exact superpose b10e32 b10e15
              | exact resolve b10e15 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e34 : y = (k x y) := by
              first
              | (have i₁ := b10e33
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e33
              | exact resolve b10e33 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e54 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b10e57 : x = (k x y) := by
              first
              | (have r₁ := b10e54
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e54 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e54
            have b10e61 : x = y := by
              first
              | (have i₁ := b10e34
                 have i₂ := b10e57
                 grind)
              | exact superpose b10e57 b10e34
              | exact resolve b10e34 b10e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34
            have b10e64 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e57
                 grind)
              | exact superpose b10e57 b10e25
              | exact resolve b10e25 b10e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e57
            have b10e65 : x ≠ y := by
              first
              | (have i₁ := b10e64
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e64
              | exact resolve b10e64 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e64
            have b10e66 : False := by grind
            exact b10e66
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : x ≠ (M.op y x) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b11e25 : (k x y) ≠ (M.op x (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e30 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b11e29
            have b11e31 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e30
              | exact resolve b11e30 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e15
              | exact resolve b11e15 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e33 : y = (k x y) := by
              first
              | (have i₁ := b11e32
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e32
              | exact resolve b11e32 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e47 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b11e49 : x = (k x y) := by
              first
              | (have r₁ := b11e47
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e47 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e47
            have b11e51 : x = y := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e49
                 grind)
              | exact superpose b11e49 b11e33
              | exact resolve b11e33 b11e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33
            have b11e54 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b11e25
                 have i₂ := b11e49
                 grind)
              | exact superpose b11e49 b11e25
              | exact resolve b11e25 b11e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e49
            have b11e55 : x ≠ y := by
              first
              | (have i₁ := b11e54
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e54
              | exact resolve b11e54 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e54
            have b11e57 : False := by grind
            exact b11e57
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
          · have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e22 : x ≠ (M.op y x) := by grind
            have b12e23 : y = (M.op x x) := by grind
            have b12e26 : (k x y) = (M.op x (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e54 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b12e61 : x = (k x y) := by
              first
              | (have r₁ := b12e54
                 have r₂ := b12e22
                 grind)
              | exact resolve b12e54 b12e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e54
            have b12e64 : x = (M.op x x) := by
              first
              | (have i₁ := b12e26
                 have i₂ := b12e61
                 grind)
              | exact superpose b12e61 b12e26
              | exact resolve b12e26 b12e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e61
            have b12e115 : x = y := by
              first
              | (have i₁ := b12e23
                 have i₂ := b12e64
                 grind)
              | exact superpose b12e64 b12e23
              | exact resolve b12e23 b12e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e131 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e115
                 grind)
              | exact superpose b12e115 b12e22
              | exact resolve b12e22 b12e115
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e115
            have b12e142 : False := by grind
            exact b12e142
          · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e23 : x ≠ (M.op y x) := by grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e27 : (k x y) ≠ (M.op x (k x y)) := by grind
              have b13e28 : x = (M.op (k x y) (k x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e60 : x = (k x y) ∨ x = (M.op y x) := by grind
              have b13e63 : x = (k x y) := by
                first
                | (have r₁ := b13e60
                   have r₂ := b13e23
                   grind)
                | exact resolve b13e60 b13e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e60
              have b13e68 : x = (M.op x x) := by
                first
                | (have i₁ := b13e28
                   have i₂ := b13e63
                   grind)
                | exact superpose b13e63 b13e28
                | exact resolve b13e28 b13e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e69 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e63
                   grind)
                | exact superpose b13e63 b13e27
                | exact resolve b13e27 b13e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e63
              have b13e70 : x ≠ y := by
                first
                | (have i₁ := b13e69
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e69
                | exact resolve b13e69 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e69
              have b13e104 : x = y := by
                first
                | (have i₁ := b13e24
                   have i₂ := b13e68
                   grind)
                | exact superpose b13e68 b13e24
                | exact resolve b13e24 b13e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e68
              have b13e109 : False := by grind
              exact b13e109
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X0 X0) X1) X3
                   have i₂ := b14e15 X0 X1 (M.op X2 X2)
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e44 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e42 X0 X1 x X3
                   have i₂ := b14e15 X0 X1 x
                   grind)
                | exact superpose b14e15 b14e42
                | exact resolve b14e42 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42
              have b14e92 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e44 x x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e44
                | exact resolve b14e44 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e93 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b14e44 (σ x) (σ x) x
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e44
                | exact resolve b14e44 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44
              have b14e169 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e93 (σ x)
                   grind)
                | exact superpose b14e93 b14e22
                | exact resolve b14e22 b14e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e93
              have b14e182 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b14e169
                   have i₂ := b14e92 x
                   grind)
                | exact superpose b14e92 b14e169
                | exact resolve b14e169 b14e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e92 b14e169
              have b14e183 : False := by grind
              exact b14e183
        · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
          · have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e22 : x ≠ (M.op y x) := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e26 : (k x y) = (M.op x (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e51 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b15e56 : x = (k x y) := by
              first
              | (have r₁ := b15e51
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e51 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e51
            have b15e58 : x = (M.op x x) := by
              first
              | (have i₁ := b15e26
                 have i₂ := b15e56
                 grind)
              | exact superpose b15e56 b15e26
              | exact resolve b15e26 b15e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e56
            have b15e107 : x = y := by
              first
              | (have i₁ := b15e23
                 have i₂ := b15e58
                 grind)
              | exact superpose b15e58 b15e23
              | exact resolve b15e23 b15e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e123 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e107
                 grind)
              | exact superpose b15e107 b15e22
              | exact resolve b15e22 b15e107
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e107
            have b15e133 : False := by grind
            exact b15e133
          · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
            · have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e23 : x ≠ (M.op y x) := by grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e27 : (k x y) ≠ (M.op x (k x y)) := by grind
              have b16e28 : x = (M.op (k x y) (k x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e53 : x = (k x y) ∨ x = (M.op y x) := by grind
              have b16e60 : x = (k x y) := by
                first
                | (have r₁ := b16e53
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e53 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e53
              have b16e61 : x = (M.op x x) := by
                first
                | (have i₁ := b16e28
                   have i₂ := b16e60
                   grind)
                | exact superpose b16e60 b16e28
                | exact resolve b16e28 b16e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e62 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e60
                   grind)
                | exact superpose b16e60 b16e27
                | exact resolve b16e27 b16e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e60
              have b16e63 : x ≠ y := by
                first
                | (have i₁ := b16e62
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e62
                | exact resolve b16e62 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e62
              have b16e112 : x = y := by
                first
                | (have i₁ := b16e24
                   have i₂ := b16e61
                   grind)
                | exact superpose b16e61 b16e24
                | exact resolve b16e24 b16e61
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e61
              have b16e118 : False := by grind
              exact b16e118
            · have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : x ≠ (M.op y x) := by grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e51 : x = (k x y) ∨ x = (M.op y x) := by grind
              have b17e56 : x = (k x y) := by
                first
                | (have r₁ := b17e51
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e51 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e51
              have b17e77 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
                | exact resolve b17e26 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e519 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e77 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e77
              have b17e520 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e519
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e519 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e519
              have b17e521 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e520
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e520
                | exact resolve b17e520 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e520
              have b17e522 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e521
                   have i₂ := b17e56
                   grind)
                | exact superpose b17e56 b17e521
                | exact resolve b17e521 b17e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56 b17e521
              have b17e523 : False := by grind
              exact b17e523
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op y x) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X2 (M.op (M.op X0 X0) X1) X3
               have i₂ := b18e13 X0 X1 (M.op X2 X2)
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e40 X0 X1 x X3
               have i₂ := b18e13 X0 X1 x
               grind)
            | exact superpose b18e13 b18e40
            | exact resolve b18e40 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e40
          have b18e74 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e42 (σ y) (σ x) x
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e42
            | exact resolve b18e42 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e82 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 X1 x
               have i₂ := b18e42 (M.op X0 X0) X1 x
               grind)
            | exact superpose b18e42 b18e13
            | exact resolve b18e13 b18e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e415 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e16 (σ x) X0
               have i₂ := b18e74 X0
               grind)
            | exact superpose b18e74 b18e16
            | (have j0 := b18e16 (σ x) X0
               grind)
            | (have r₁ := b18e16 (σ x) X0
               have r₂ := b18e74 X0
               grind)
            | exact resolve b18e16 b18e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e74
          have b18e421 : ∀ X0 : G, (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b18e415 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e415
          have b18e549 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e19 x X0
               have i₂ := b18e421 (σ X0)
               grind)
            | exact superpose b18e421 b18e19
            | exact resolve b18e19 b18e421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e421
          have b18e707 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b18e14 (k x X0)
               have i₂ := b18e549 X0
               grind)
            | exact superpose b18e549 b18e14
            | exact resolve b18e14 b18e549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e549
          have b18e716 : ∀ X0 : G, (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e707 X0
               have i₂ := b18e14 X0
               grind)
            | exact superpose b18e14 b18e707
            | exact resolve b18e707 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e707
          have b18e766 : x = (M.op x x) ∨ x = (M.op (M.op x x) x) := by grind
          clear b18e716
          have b18e771 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b18e766
               have i₂ := b18e82 x x
               grind)
            | exact superpose b18e82 b18e766
            | exact resolve b18e766 b18e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e82 b18e766
          have b18e772 : x = (M.op x x) := by grind
          clear b18e771
          have b18e818 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b18e42 x x x
               have i₂ := b18e772
               grind)
            | exact superpose b18e772 b18e42
            | exact resolve b18e42 b18e772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42 b18e772
          have b18e851 : x ≠ x := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e818 y
               grind)
            | exact superpose b18e818 b18e21
            | (have r₁ := b18e21
               have r₂ := b18e818 y
               grind)
            | exact resolve b18e21 b18e818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e818
          have b18e869 : False := by grind
          exact b18e869
        · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e23 : y ≠ (M.op x x) := by grind
            have b19e25 : (k x y) ≠ (M.op x (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e46 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X2 (M.op (M.op X0 X0) X1) X3
                 have i₂ := b19e14 X0 X1 (M.op X2 X2)
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e48 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b19e46 X0 X1 x X3
                 have i₂ := b19e14 X0 X1 x
                 grind)
              | exact superpose b19e14 b19e46
              | exact resolve b19e46 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e46
            have b19e66 : (M.op y x) ≠ (M.op x (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b19e25
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e25
              | (have j1 := b19e19 x y
                 grind)
              | (have r₁ := b19e25
                 have r₂ := b19e19 (k x y) x
                 grind)
              | exact resolve b19e25 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e79 : y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b19e66
                 have r₂ := b19e48 y x x
                 grind)
              | exact resolve b19e66 b19e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e48 b19e66
            have b19e86 : x = (M.op y x) := by
              first
              | (have r₁ := b19e79
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e79 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e79
            have b19e92 : False := by grind
            exact b19e92
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e23 : y ≠ (M.op x x) := by grind
            have b20e25 : (k x y) ≠ (M.op x (k x y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X2 (M.op (M.op X0 X0) X1) X3
                 have i₂ := b20e14 X0 X1 (M.op X2 X2)
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e44 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e42 X0 X1 x X3
                 have i₂ := b20e14 X0 X1 x
                 grind)
              | exact superpose b20e14 b20e42
              | exact resolve b20e42 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e42
            have b20e65 : (M.op y x) ≠ (M.op x (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e25
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e25
              | (have j1 := b20e19 x y
                 grind)
              | (have r₁ := b20e25
                 have r₂ := b20e19 (k x y) x
                 grind)
              | exact resolve b20e25 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e78 : y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b20e65
                 have r₂ := b20e44 y x x
                 grind)
              | exact resolve b20e65 b20e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e44 b20e65
            have b20e84 : x = (M.op y x) := by
              first
              | (have r₁ := b20e78
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e78 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e78
            have b20e89 : False := by grind
            exact b20e89
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op y x) := by grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e50 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b21e54 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e50
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e50 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e55 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e54
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e54
              | exact resolve b21e54 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e58 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e55
                 grind)
              | exact superpose b21e55 b21e15
              | exact resolve b21e15 b21e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e55
            have b21e59 : x = (k x y) := by
              first
              | (have i₁ := b21e58
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e58
              | exact resolve b21e58 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e58
            have b21e86 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e59
                 grind)
              | exact superpose b21e59 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e59
            have b21e87 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b21e86
            have b21e89 : y = (M.op x x) := by
              first
              | (have r₁ := b21e87
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e87 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e87
            have b21e91 : False := by grind
            exact b21e91
          · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b22e23 : x ≠ (M.op y x) := by grind
              have b22e28 : x = (M.op (k x y) (k x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 X2 (M.op (M.op X0 X0) X1) X3
                   have i₂ := b22e15 X0 X1 (M.op X2 X2)
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b22e38 X0 X1 x X3
                   have i₂ := b22e15 X0 X1 x
                   grind)
                | exact superpose b22e15 b22e38
                | exact resolve b22e38 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e38
              have b22e42 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b22e40 (k x y) (k x y) x
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e40
                | exact resolve b22e40 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e40
              have b22e59 : x ≠ x := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e42 y
                   grind)
                | exact superpose b22e42 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e42 y
                   grind)
                | exact resolve b22e23 b22e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e42
              have b22e67 : False := by grind
              exact b22e67
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e23 : x ≠ (M.op y x) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e27 : (k x y) ≠ (M.op x (k x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X2 (M.op (M.op X0 X0) X1) X3
                   have i₂ := b23e15 X0 X1 (M.op X2 X2)
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b23e36 X0 X1 x X3
                   have i₂ := b23e15 X0 X1 x
                   grind)
                | exact superpose b23e15 b23e36
                | exact resolve b23e36 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36
              have b23e67 : (M.op y x) ≠ (M.op x (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e27
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e27
                | (have j1 := b23e20 x y
                   grind)
                | (have r₁ := b23e27
                   have r₂ := b23e20 (k x y) x
                   grind)
                | exact resolve b23e27 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e81 : y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e67
                   have r₂ := b23e38 y x x
                   grind)
                | exact resolve b23e67 b23e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38 b23e67
              have b23e85 : x = (M.op y x) := by
                first
                | (have r₁ := b23e81
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e81 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e81
              have b23e88 : False := by grind
              exact b23e88
        · rcases eq_or_ne (M.op x (k x y)) ((k x y)) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : x ≠ (M.op y x) := by grind
            have b24e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 (τ X0) X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X0 X0) X1) X3
                 have i₂ := b24e14 X0 X1 (M.op X2 X2)
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b24e33 X0 X1 x X3
                 have i₂ := b24e14 X0 X1 x
                 grind)
              | exact superpose b24e14 b24e33
              | exact resolve b24e33 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 X1 x
                 have i₂ := b24e35 (M.op X0 X0) X1 x
                 grind)
              | exact superpose b24e35 b24e14
              | exact resolve b24e14 b24e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e17 (M.op X0 X1) X2
                 have i₂ := b24e35 X0 X1 X2
                 grind)
              | exact superpose b24e35 b24e17
              | (have j0 := b24e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b24e17 (M.op X0 X1) x
                 have r₂ := b24e35 X0 X1 x
                 grind)
              | exact resolve b24e17 b24e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e44 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b24e42 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42
            have b24e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e66 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e35 X0 X0 x
                 have i₂ := b24e19 X0 X1
                 grind)
              | (have i₁ := b24e35 X0 X1 x
                 have i₂ := b24e19 X0 (M.op X0 X1)
                 grind)
              | exact superpose b24e19 b24e35
              | (have j1 := b24e19 X1 X0
                 grind)
              | exact resolve b24e35 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e84 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e15 (k (τ X0) X1)
                 have i₂ := b24e30 X0 X1
                 grind)
              | exact superpose b24e30 b24e15
              | exact resolve b24e15 b24e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e30
            have b24e101 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 X2)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e31 X0 (M.op X1 X2)
                 have i₂ := b24e44 X1 X2 (τ X0)
                 grind)
              | exact superpose b24e44 b24e31
              | exact resolve b24e31 b24e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31
            have b24e111 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 X2)) X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e101 X0 X1 X2
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e101
              | exact resolve b24e101 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e101
            have b24e121 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) (σ (M.op X0 X1))) := by
              intro X0 X1
              grind
            clear b24e111
            have b24e125 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e121 X0 X1
                 have i₂ := b24e40 (σ (M.op X0 X1)) (σ (M.op X0 X1))
                 grind)
              | exact superpose b24e40 b24e121
              | (have j0 := b24e121 X0 X1
                 grind)
              | exact resolve b24e121 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e121
            have b24e126 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have j0 := b24e125 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e125
            have b24e502 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e84 (M.op X1 X2) X0
                 have i₂ := b24e44 X1 X2 (σ X0)
                 grind)
              | exact superpose b24e44 b24e84
              | exact resolve b24e84 b24e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e44 b24e84
            have b24e518 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e502 X0 X1 X2
                 have i₂ := b24e15 X0
                 grind)
              | exact superpose b24e15 b24e502
              | exact resolve b24e502 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e502
            have b24e544 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) (τ (M.op X0 X1))) := by
              intro X0 X1
              grind
            clear b24e518
            have b24e549 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e544 X0 X1
                 have i₂ := b24e40 (τ (M.op X0 X1)) (τ (M.op X0 X1))
                 grind)
              | exact superpose b24e40 b24e544
              | (have j0 := b24e544 X0 X1
                 grind)
              | exact resolve b24e544 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e40 b24e544
            have b24e550 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have j0 := b24e549 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e549
            have b24e617 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e35 (σ X1) (σ X1) x
                 have i₂ := b24e60 X0 X1
                 grind)
              | exact superpose b24e60 b24e35
              | (have j1 := b24e60 X0 X1
                 grind)
              | exact resolve b24e35 b24e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e60
            have b24e1649 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X1 X0 X2
                 have i₂ := b24e66 X0 X3 (M.op X1 X1)
                 grind)
              | exact superpose b24e66 b24e14
              | (have j1 := b24e66 X0 X3 X2
                 grind)
              | exact resolve b24e14 b24e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e4733 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e35 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
                 have i₂ := b24e126 X0 X1
                 grind)
              | exact superpose b24e126 b24e35
              | exact resolve b24e35 b24e126
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e126
            have b24e5874 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e35 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                 have i₂ := b24e550 X0 X1
                 grind)
              | exact superpose b24e550 b24e35
              | exact resolve b24e35 b24e550
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e35 b24e550
            have b24e7249 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b24e24
                 have i₂ := b24e617 x X0 (σ y)
                 grind)
              | exact superpose b24e617 b24e24
              | (have j1 := b24e617 x X0 x
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e617 x x (σ y)
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e617 y x x
                 grind)
              | exact resolve b24e24 b24e617
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e617
            have b24e7327 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e7249 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e7249
            have b24e44775 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e7327 y
                 grind)
              | exact superpose b24e7327 b24e21
              | (have j1 := b24e7327 y
                 grind)
              | exact resolve b24e21 b24e7327
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e7327
            have b24e46443 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e22
                 have i₂ := b24e1649 x y X0 X1
                 grind)
              | (have i₁ := b24e22
                 have i₂ := b24e1649 x X0 y X1
                 grind)
              | exact superpose b24e1649 b24e22
              | (have j1 := b24e1649 x X1 x X1
                 grind)
              | (have r₁ := b24e22
                 have r₂ := b24e1649 y X1 x x
                 grind)
              | exact resolve b24e22 b24e1649
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1649
            have b24e46684 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
              intro X1
              first
              | (have j0 := b24e46443 x X1
                 have j1 := b24e66 x X1 x
                 grind)
              | (have r₁ := b24e46443 x X1
                 have r₂ := b24e66 x X1 x
                 grind)
              | (have r₁ := b24e46443 x X1
                 have r₂ := b24e66 x x x
                 grind)
              | exact resolve b24e46443 b24e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e66 b24e46443
            have b24e89119 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b24e44775
                 have i₂ := b24e46684 y
                 grind)
              | exact superpose b24e46684 b24e44775
              | (have j1 := b24e46684 y
                 grind)
              | exact resolve b24e44775 b24e46684
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e44775 b24e46684
            have b24e89135 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
            clear b24e89119
            have b24e89179 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b24e5874 (σ x) (σ y) x
                 have i₂ := b24e89135
                 grind)
              | exact superpose b24e89135 b24e5874
              | exact resolve b24e5874 b24e89135
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5874 b24e89135
            have b24e89192 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
              intro X0
              first
              | (have i₁ := b24e89179 X0
                 have i₂ := b24e15 y
                 grind)
              | exact superpose b24e15 b24e89179
              | exact resolve b24e89179 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e89179
            have b24e89365 : y ≠ y ∨ y = (M.op x y) := by
              first
              | (have j0 := b24e89192 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e89192
            have b24e89366 : y = (M.op x y) := by grind
            clear b24e89365
            have b24e89459 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b24e4733 x y x
                 have i₂ := b24e89366
                 grind)
              | exact superpose b24e89366 b24e4733
              | exact resolve b24e4733 b24e89366
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4733
            have b24e91634 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e89459 (σ x)
                 grind)
              | exact superpose b24e89459 b24e21
              | exact resolve b24e21 b24e89459
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e89459
            have b24e91776 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b24e91634
                 have i₂ := b24e89366
                 grind)
              | exact superpose b24e89366 b24e91634
              | exact resolve b24e91634 b24e89366
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e89366 b24e91634
            have b24e91777 : False := by grind
            exact b24e91777
          · rcases eq_or_ne (M.op (k x y) (k x y)) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b25e23 : x ≠ (M.op y x) := by grind
              have b25e28 : x = (M.op (k x y) (k x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X0 X0) X1) X3
                   have i₂ := b25e15 X0 X1 (M.op X2 X2)
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e35 X0 X1 x X3
                   have i₂ := b25e15 X0 X1 x
                   grind)
                | exact superpose b25e15 b25e35
                | exact resolve b25e35 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e38 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b25e37 (k x y) (k x y) x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e37
                | exact resolve b25e37 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37
              have b25e52 : x ≠ x := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e38 y
                   grind)
                | exact superpose b25e38 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e38 y
                   grind)
                | exact resolve b25e23 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e60 : False := by grind
              exact b25e60
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e23 : x ≠ (M.op y x) := by grind
              have b26e24 : y ≠ (M.op x x) := by grind
              have b26e27 : (k x y) ≠ (M.op x (k x y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X0 X0) X1) X3
                   have i₂ := b26e15 X0 X1 (M.op X2 X2)
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e33 X0 X1 x X3
                   have i₂ := b26e15 X0 X1 x
                   grind)
                | exact superpose b26e15 b26e33
                | exact resolve b26e33 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e59 : (M.op y x) ≠ (M.op x (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b26e27
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e27
                | (have j1 := b26e20 x y
                   grind)
                | (have r₁ := b26e27
                   have r₂ := b26e20 (k x y) x
                   grind)
                | exact resolve b26e27 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e72 : y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b26e59
                   have r₂ := b26e35 y x x
                   grind)
                | exact resolve b26e59 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e59
              have b26e74 : x = (M.op y x) := by
                first
                | (have r₁ := b26e72
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e72 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72
              have b26e76 : False := by grind
              exact b26e76

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_x_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b0e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e22 : (M.op x y) = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b0e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e32 X0 X1 x X3
             have i₂ := b0e12 X0 X1 x
             grind)
          | exact superpose b0e12 b0e32
          | exact resolve b0e32 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e32
        have b0e68 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b0e15 X0 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 X0 x
             grind)
          | (have r₁ := b0e15 y x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b0e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b0e18 X0 X0
             have i₂ := b0e69 (σ X0)
             grind)
          | exact superpose b0e69 b0e18
          | exact resolve b0e18 b0e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b0e83 X0
             have i₂ := b0e69 X0
             grind)
          | exact superpose b0e69 b0e83
          | exact resolve b0e83 b0e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e69 b0e83
        have b0e136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e17 X0 X1
             grind)
          | (have i₁ := b0e16 X0 X0
             have i₂ := b0e17 X0 X1
             grind)
          | exact superpose b0e17 b0e16
          | (have j0 := b0e16 X0 X1
             have j1 := b0e17 X0 X1
             grind)
          | (have r₁ := b0e16 X1 X1
             have r₂ := b0e17 X1 X1
             grind)
          | (have r₁ := b0e16 X0 X0
             have r₂ := b0e17 X0 X0
             grind)
          | (have r₁ := b0e16 X0 X1
             have r₂ := b0e17 X0 X1
             grind)
          | exact resolve b0e16 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X1 X0
             have i₂ := b0e17 (σ X1) (σ X0)
             grind)
          | exact superpose b0e17 b0e18
          | (have j1 := b0e17 (σ X1) (σ X0)
             grind)
          | exact resolve b0e18 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e153 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b0e17 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e155 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b0e136 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e136
        have b0e158 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e149 X0 X1
             have i₂ := b0e86 X0
             grind)
          | exact superpose b0e86 b0e149
          | (have j0 := b0e149 X0 X1
             grind)
          | exact resolve b0e149 b0e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e149
        have b0e160 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b0e155 X0 X1
             have j1 := b0e153 X1 X0
             grind)
          | (have r₁ := b0e155 X0 X1
             have r₂ := b0e153 X0 X1
             grind)
          | (have r₁ := b0e155 X1 X0
             have r₂ := b0e153 X0 X1
             grind)
          | (have r₁ := b0e155 X0 X0
             have r₂ := b0e153 X0 X0
             grind)
          | exact resolve b0e155 b0e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e153 b0e155
        have b0e169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e158 X0 X1
             have i₂ := b0e86 X1
             grind)
          | exact superpose b0e86 b0e158
          | (have j0 := b0e158 X0 X1
             grind)
          | exact resolve b0e158 b0e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e158
        have b0e325 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b0e33 (σ X0) (σ X0) x
             have i₂ := b0e86 X0
             grind)
          | exact superpose b0e86 b0e33
          | exact resolve b0e33 b0e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e361 : (M.op y y) = (k y x) := by
          first
          | (have j0 := b0e68 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e68
        have b0e400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e160 (σ X0) (σ X1)
             have i₂ := b0e18 X0 X1
             grind)
          | exact superpose b0e18 b0e160
          | (have j0 := b0e160 (σ X0) (σ X1)
             grind)
          | exact resolve b0e160 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e160
        have b0e467 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e400 X0 X1
             have i₂ := b0e86 X1
             grind)
          | exact superpose b0e86 b0e400
          | (have j0 := b0e400 X0 X1
             grind)
          | exact resolve b0e400 b0e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e400
        have b0e1268 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b0e169 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e169
        have b0e14138 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 (σ X0) (σ X1)
             have i₂ := b0e467 X0 X1
             grind)
          | exact superpose b0e467 b0e16
          | (have j0 := b0e16 (σ X0) (σ X1)
             have j1 := b0e467 X0 X1
             grind)
          | exact resolve b0e16 b0e467
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e14295 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b0e467 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e14384 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e14138 X0 X1
             have i₂ := b0e86 X0
             grind)
          | exact superpose b0e86 b0e14138
          | (have j0 := b0e14138 X0 X1
             grind)
          | exact resolve b0e14138 b0e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e14138
        have b0e14517 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e14384 X0 X1
             have i₂ := b0e86 X1
             grind)
          | exact superpose b0e86 b0e14384
          | (have j0 := b0e14384 X0 X1
             grind)
          | exact resolve b0e14384 b0e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e86 b0e14384
        have b0e14598 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b0e14517 X0 X1
             have j1 := b0e14295 X1 X0
             grind)
          | (have r₁ := b0e14517 X1 X0
             have r₂ := b0e14295 X0 X1
             grind)
          | (have r₁ := b0e14517 (M.op X0 X0) X0
             have r₂ := b0e14295 X0 (M.op X0 X0)
             grind)
          | exact resolve b0e14517 b0e14295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e14295 b0e14517
        have b0e14655 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e14598 X0 X1
             have i₂ := b0e18 X0 X1
             grind)
          | exact superpose b0e18 b0e14598
          | (have j0 := b0e14598 X0 X1
             grind)
          | exact resolve b0e14598 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e14598
        have b0e14656 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have j0 := b0e14655 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e14655
        have b0e25814 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b0e1268 x y
             have i₂ := b0e361
             grind)
          | exact superpose b0e361 b0e1268
          | (have j0 := b0e1268 x y
             grind)
          | exact resolve b0e1268 b0e361
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1268
        have b0e25884 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
        clear b0e25814
        have b0e25933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b0e25884
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e25884
          | exact resolve b0e25884 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e25884
        have b0e26005 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b0e25933
             have r₂ := b0e19
             grind)
          | exact resolve b0e25933 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e25933
        have b0e26129 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b0e26005
             have i₂ := b0e467 y x
             grind)
          | exact superpose b0e467 b0e26005
          | (have j1 := b0e467 y x
             grind)
          | exact resolve b0e26005 b0e467
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e467 b0e26005
        have b0e26215 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have j1 := b0e14656 y x
             grind)
          | (have r₁ := b0e26129
             have r₂ := b0e14656 y x
             grind)
          | exact resolve b0e26129 b0e14656
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e14656 b0e26129
        have b0e26227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b0e26215
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e26215
          | exact resolve b0e26215 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26215
        have b0e26232 : (σ y) = (σ (k y x)) := by
          first
          | (have r₁ := b0e26227
             have r₂ := b0e19
             grind)
          | exact resolve b0e26227 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26227
        have b0e26237 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b0e26232
             have i₂ := b0e361
             grind)
          | exact superpose b0e361 b0e26232
          | exact resolve b0e26232 b0e361
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e361 b0e26232
        have b0e26488 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e325 y x
             have i₂ := b0e26237
             grind)
          | exact superpose b0e26237 b0e325
          | exact resolve b0e325 b0e26237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e325
        have b0e26501 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b0e13 (M.op y y)
             have i₂ := b0e26237
             grind)
          | exact superpose b0e26237 b0e13
          | exact resolve b0e13 b0e26237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26237
        have b0e26577 : y = (M.op y y) := by
          first
          | (have i₁ := b0e26501
             have i₂ := b0e13 y
             grind)
          | exact superpose b0e13 b0e26501
          | exact resolve b0e26501 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26501
        have b0e26920 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e33 y y x
             have i₂ := b0e26577
             grind)
          | exact superpose b0e26577 b0e33
          | exact resolve b0e33 b0e26577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33 b0e26577
        have b0e32615 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e26488 (σ x)
             grind)
          | exact superpose b0e26488 b0e19
          | exact resolve b0e19 b0e26488
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26488
        have b0e32821 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e32615
             have i₂ := b0e26920 x
             grind)
          | exact superpose b0e26920 b0e32615
          | exact resolve b0e32615 b0e26920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26920 b0e32615
        have b0e32822 : False := by grind
        exact b0e32822
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e23 : (M.op x y) ≠ (M.op x x) := by grind
          have b1e24 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e23
            | exact resolve b1e23 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e20
            | exact resolve b1e20 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b1e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e32 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e32
            | exact resolve b1e32 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32
          have b1e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 X1 x
               have i₂ := b1e33 (M.op X0 X1) X1 x
               grind)
            | exact superpose b1e33 b1e13
            | exact resolve b1e13 b1e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b1e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e19 X0 X0
               have i₂ := b1e67 (σ X0)
               grind)
            | exact superpose b1e67 b1e19
            | exact resolve b1e19 b1e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b1e78 X0
               have i₂ := b1e67 X0
               grind)
            | exact superpose b1e67 b1e78
            | exact resolve b1e78 b1e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e67 b1e78
          have b1e84 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) := by
            first
            | (have i₁ := b1e17 y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e17
            | (have j0 := b1e17 y y
               grind)
            | (have r₁ := b1e17 y x
               have r₂ := b1e24
               grind)
            | exact resolve b1e17 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e88 : (M.op y y) = (M.op x x) ∨ y = (k y x) := by grind
          clear b1e84
          have b1e91 : y = (k y x) := by
            first
            | (have r₁ := b1e88
               have r₂ := b1e25
               grind)
            | exact resolve b1e88 b1e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25 b1e88
          have b1e143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 X0
               have i₂ := b1e18 (σ X1) (σ X0)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X0)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e151 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e143 X0 X1
               have i₂ := b1e79 X0
               grind)
            | exact superpose b1e79 b1e143
            | (have j0 := b1e143 X0 X1
               grind)
            | exact resolve b1e143 b1e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e143
          have b1e163 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e151 X0 X1
               have i₂ := b1e79 X1
               grind)
            | exact superpose b1e79 b1e151
            | (have j0 := b1e151 X0 X1
               grind)
            | exact resolve b1e151 b1e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e151
          have b1e234 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b1e33 (σ X0) (σ X0) x
               have i₂ := b1e79 X0
               grind)
            | exact superpose b1e79 b1e33
            | exact resolve b1e33 b1e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e235 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b1e40 (σ X0) (σ X0)
               have i₂ := b1e79 X0
               grind)
            | exact superpose b1e79 b1e40
            | exact resolve b1e40 b1e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e40
          have b1e240 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e16 X1 (σ X0)
               have i₂ := b1e79 X0
               grind)
            | exact superpose b1e79 b1e16
            | (have j0 := b1e16 X1 (σ X0)
               grind)
            | exact resolve b1e16 b1e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e1164 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e33 (σ X0) (σ X1) x
               have i₂ := b1e163 X0 X1
               grind)
            | exact superpose b1e163 b1e33
            | (have j1 := b1e163 X1 X0
               grind)
            | exact resolve b1e33 b1e163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e33
          have b1e1178 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b1e163 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e163
          have b1e23202 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e1178 x y
               have i₂ := b1e91
               grind)
            | exact superpose b1e91 b1e1178
            | (have j0 := b1e1178 x y
               grind)
            | exact resolve b1e1178 b1e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1178
          have b1e23299 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b1e23202
               have r₂ := b1e26
               grind)
            | exact resolve b1e23202 b1e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e23202
          have b1e29362 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b1e1164 y x x
               have i₂ := b1e91
               grind)
            | exact superpose b1e91 b1e1164
            | (have j0 := b1e1164 y x x
               grind)
            | exact resolve b1e1164 b1e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1164
          have b1e30580 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            intro X0
            first
            | (have j0 := b1e29362 X0
               grind)
            | (have r₁ := b1e29362 X0
               have r₂ := b1e26
               grind)
            | exact resolve b1e29362 b1e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e29362
          have b1e30971 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e235 y
               have i₂ := b1e30580 (σ (M.op y y))
               grind)
            | exact superpose b1e30580 b1e235
            | exact resolve b1e235 b1e30580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e235 b1e30580
          have b1e31074 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b1e30971
               have r₂ := b1e23299
               grind)
            | exact resolve b1e30971 b1e23299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e23299 b1e30971
          have b1e32639 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b1e240 x (σ y)
               have i₂ := b1e31074
               grind)
            | exact superpose b1e31074 b1e240
            | (have j0 := b1e240 x (σ y)
               grind)
            | (have r₁ := b1e240 x (σ y)
               have r₂ := b1e31074
               grind)
            | exact resolve b1e240 b1e31074
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e240 b1e31074
          have b1e32697 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b1e32639
          have b1e32715 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b1e32697
               have i₂ := b1e19 y x
               grind)
            | exact superpose b1e19 b1e32697
            | exact resolve b1e32697 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32697
          have b1e32730 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e32715
               have i₂ := b1e91
               grind)
            | exact superpose b1e91 b1e32715
            | exact resolve b1e32715 b1e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e91 b1e32715
          have b1e32740 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b1e32730
               have i₂ := b1e79 y
               grind)
            | exact superpose b1e79 b1e32730
            | exact resolve b1e32730 b1e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e79 b1e32730
          have b1e34295 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e234 y x
               have i₂ := b1e32740
               grind)
            | exact superpose b1e32740 b1e234
            | exact resolve b1e234 b1e32740
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e234
          have b1e38921 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e34295 (σ x)
               grind)
            | exact superpose b1e34295 b1e26
            | exact resolve b1e26 b1e34295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26 b1e34295
          have b1e38957 : False := by grind
          exact b1e38957
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : (M.op y x) = (M.op y y) := by grind
          have b2e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          have b2e23 : (M.op x y) ≠ (M.op x x) := by grind
          have b2e24 : (M.op x y) ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b2e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e30 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e29 X0 X1 x X3
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e29
            | exact resolve b2e29 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e29
          have b2e36 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 X1 x
               have i₂ := b2e30 (M.op X0 X1) X1 x
               grind)
            | exact superpose b2e30 b2e13
            | exact resolve b2e13 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30
          have b2e58 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e16 (σ x) (σ y)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e16
            | (have j0 := b2e16 (σ y) (σ y)
               grind)
            | (have r₁ := b2e16 (σ x) (σ y)
               have r₂ := b2e22
               grind)
            | exact resolve b2e16 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e59 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b2e16 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 y y
               grind)
            | (have r₁ := b2e16 x y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b2e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e63 : (M.op x x) = (k x y) := by grind
          clear b2e59
          have b2e64 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear b2e58
          have b2e66 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b2e64
               have i₂ := b2e19 x y
               grind)
            | exact superpose b2e19 b2e64
            | exact resolve b2e64 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e64
          have b2e70 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b2e66
               have i₂ := b2e63
               grind)
            | exact superpose b2e63 b2e66
            | exact resolve b2e66 b2e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63 b2e66
          have b2e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 X0 X0
               have i₂ := b2e62 (σ X0)
               grind)
            | exact superpose b2e62 b2e19
            | exact resolve b2e19 b2e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b2e73 X0
               have i₂ := b2e62 X0
               grind)
            | exact superpose b2e62 b2e73
            | exact resolve b2e73 b2e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e62 b2e73
          have b2e122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e17 X0 X1
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e17 X0 X0
               have i₂ := b2e18 X0 X1
               grind)
            | exact superpose b2e18 b2e17
            | (have j0 := b2e17 X0 X1
               have j1 := b2e18 X0 X1
               grind)
            | (have r₁ := b2e17 X1 X1
               have r₂ := b2e18 X1 X1
               grind)
            | (have r₁ := b2e17 X0 X0
               have r₂ := b2e18 X0 X0
               grind)
            | (have r₁ := b2e17 X0 X1
               have r₂ := b2e18 X0 X1
               grind)
            | exact resolve b2e17 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e135 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 X0
               have i₂ := b2e18 (σ X1) (σ X0)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X1) (σ X0)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e138 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b2e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e141 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b2e122 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e122
          have b2e145 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e135 X0 X1
               have i₂ := b2e74 X0
               grind)
            | exact superpose b2e74 b2e135
            | (have j0 := b2e135 X0 X1
               grind)
            | exact resolve b2e135 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e135
          have b2e147 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b2e141 X0 X1
               have j1 := b2e138 X1 X0
               grind)
            | (have r₁ := b2e141 X0 X1
               have r₂ := b2e138 X0 X1
               grind)
            | (have r₁ := b2e141 X1 X0
               have r₂ := b2e138 X0 X1
               grind)
            | (have r₁ := b2e141 X0 X0
               have r₂ := b2e138 X0 X0
               grind)
            | exact resolve b2e141 b2e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e138 b2e141
          have b2e156 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e145 X0 X1
               have i₂ := b2e74 X1
               grind)
            | exact superpose b2e74 b2e145
            | (have j0 := b2e145 X0 X1
               grind)
            | exact resolve b2e145 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e145
          have b2e206 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b2e16 X0 (σ x)
               have i₂ := b2e70
               grind)
            | exact superpose b2e70 b2e16
            | (have j0 := b2e16 X0 (σ x)
               grind)
            | exact resolve b2e16 b2e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e70
          have b2e258 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e16 X1 (σ X0)
               have i₂ := b2e74 X0
               grind)
            | exact superpose b2e74 b2e16
            | (have j0 := b2e16 X1 (σ X0)
               grind)
            | exact resolve b2e16 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e147 (σ X0) (σ X1)
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e147
            | (have j0 := b2e147 (σ X0) (σ X1)
               grind)
            | exact resolve b2e147 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e147
          have b2e347 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e291 X0 X1
               have i₂ := b2e74 X1
               grind)
            | exact superpose b2e74 b2e291
            | (have j0 := b2e291 X0 X1
               grind)
            | exact resolve b2e291 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e291
          have b2e955 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e156 x y
               grind)
            | exact superpose b2e156 b2e20
            | (have j1 := b2e156 x y
               grind)
            | exact resolve b2e20 b2e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e156
          have b2e11168 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (k X0 x)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b2e206 (σ X0)
               have i₂ := b2e347 X0 x
               grind)
            | exact superpose b2e347 b2e206
            | (have j0 := b2e206 (σ X0)
               have j1 := b2e347 X0 x
               grind)
            | (have r₁ := b2e206 (σ X0)
               have r₂ := b2e347 X0 x
               grind)
            | exact resolve b2e206 b2e347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e11209 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e17 (σ X0) (σ X1)
               have i₂ := b2e347 X0 X1
               grind)
            | exact superpose b2e347 b2e17
            | (have j0 := b2e17 (σ X0) (σ X1)
               have j1 := b2e347 X0 X1
               grind)
            | exact resolve b2e17 b2e347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e11362 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b2e347 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e11435 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e11209 X0 X1
               have i₂ := b2e74 X0
               grind)
            | exact superpose b2e74 b2e11209
            | (have j0 := b2e11209 X0 X1
               grind)
            | exact resolve b2e11209 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11209
          have b2e11438 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (k X0 x)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ x)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have j0 := b2e11168 X0
               have j1 := b2e206 (σ X0)
               grind)
            | (have r₁ := b2e11168 X0
               have r₂ := b2e206 (σ X0)
               grind)
            | exact resolve b2e11168 b2e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e206 b2e11168
          have b2e11563 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e11435 X0 X1
               have i₂ := b2e74 X1
               grind)
            | exact superpose b2e74 b2e11435
            | (have j0 := b2e11435 X0 X1
               grind)
            | exact resolve b2e11435 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11435
          have b2e11565 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) ∨ (σ (M.op x x)) ≠ (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b2e11438 X0
               have i₂ := b2e19 X0 x
               grind)
            | exact superpose b2e19 b2e11438
            | (have j0 := b2e11438 X0
               grind)
            | exact resolve b2e11438 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11438
          have b2e11643 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b2e11563 X0 X1
               have j1 := b2e11362 X1 X0
               grind)
            | (have r₁ := b2e11563 X1 X0
               have r₂ := b2e11362 X0 X1
               grind)
            | (have r₁ := b2e11563 (M.op X0 X0) X0
               have r₂ := b2e11362 X0 (M.op X0 X0)
               grind)
            | exact resolve b2e11563 b2e11362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11362 b2e11563
          have b2e11645 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 x)) ∨ (σ (M.op x x)) ≠ (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b2e11565 X0
               have i₂ := b2e74 X0
               grind)
            | exact superpose b2e74 b2e11565
            | (have j0 := b2e11565 X0
               grind)
            | exact resolve b2e11565 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11565
          have b2e11695 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e11643 X0 X1
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e11643
            | (have j0 := b2e11643 X0 X1
               grind)
            | exact resolve b2e11643 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11643
          have b2e11696 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b2e11695 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11695
          have b2e20520 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b2e955
               have i₂ := b2e18 y x
               grind)
            | exact superpose b2e18 b2e955
            | (have j1 := b2e18 y x
               grind)
            | exact resolve b2e955 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e955
          have b2e20537 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b2e20520
          have b2e20545 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b2e20537
               have r₂ := b2e23
               grind)
            | exact resolve b2e20537 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e20537
          have b2e20546 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b2e20545
               have r₂ := b2e24
               grind)
            | exact resolve b2e20545 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e20545
          have b2e61183 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e20546
               have i₂ := b2e347 y x
               grind)
            | exact superpose b2e347 b2e20546
            | (have j1 := b2e347 y x
               grind)
            | exact resolve b2e20546 b2e347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e347 b2e20546
          have b2e61331 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have j1 := b2e11645 y
               grind)
            | (have r₁ := b2e61183
               have r₂ := b2e11645 y
               grind)
            | exact resolve b2e61183 b2e11645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11645 b2e61183
          have b2e61348 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have j1 := b2e11696 y x
               grind)
            | (have r₁ := b2e61331
               have r₂ := b2e11696 y x
               grind)
            | exact resolve b2e61331 b2e11696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e11696 b2e61331
          have b2e61546 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e258 x (σ y)
               have i₂ := b2e61348
               grind)
            | exact superpose b2e61348 b2e258
            | (have j0 := b2e258 x (σ y)
               grind)
            | (have r₁ := b2e258 x (σ y)
               have r₂ := b2e61348
               grind)
            | exact resolve b2e258 b2e61348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e258 b2e61348
          have b2e61630 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by grind
          clear b2e61546
          have b2e61654 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e61630
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e61630
            | exact resolve b2e61630 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e61630
          have b2e61678 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e61654
               have i₂ := b2e74 y
               grind)
            | exact superpose b2e74 b2e61654
            | exact resolve b2e61654 b2e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e74 b2e61654
          have b2e62322 : (k y x) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e14 (k y x)
               have i₂ := b2e61678
               grind)
            | exact superpose b2e61678 b2e14
            | exact resolve b2e14 b2e61678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e61678
          have b2e62420 : (σ y) = (σ (k y x)) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b2e62322
               have i₂ := b2e14 (M.op y y)
               grind)
            | exact superpose b2e14 b2e62322
            | exact resolve b2e62322 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e62322
          have b2e62911 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b2e62420
               have i₂ := b2e18 y x
               grind)
            | exact superpose b2e18 b2e62420
            | (have j1 := b2e18 y x
               grind)
            | exact resolve b2e62420 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e62420
          have b2e63013 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b2e62911
          have b2e63053 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b2e63013
               have r₂ := b2e24
               grind)
            | exact resolve b2e63013 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63013
          have b2e63061 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b2e63053
               have r₂ := b2e23
               grind)
            | exact resolve b2e63053 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63053
          have b2e65031 : (M.op x y) = (τ (σ y)) := by
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e63061
               grind)
            | exact superpose b2e63061 b2e14
            | exact resolve b2e14 b2e63061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63061
          have b2e65147 : y = (M.op x y) := by
            first
            | (have i₁ := b2e65031
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e65031
            | exact resolve b2e65031 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e65031
          have b2e67258 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e65147
               grind)
            | exact superpose b2e65147 b2e24
            | exact resolve b2e24 b2e65147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e67262 : y = (M.op y y) := by
            first
            | (have i₁ := b2e36 x y
               have i₂ := b2e65147
               grind)
            | exact superpose b2e65147 b2e36
            | exact resolve b2e36 b2e65147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e65147
          have b2e67339 : False := by grind
          exact b2e67339
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : (M.op y x) = (M.op y y) := by grind
          have b3e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b3e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b3e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b3e36 X0 X1 x X3
               have i₂ := b3e13 X0 X1 x
               grind)
            | exact superpose b3e13 b3e36
            | exact resolve b3e36 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e36
          have b3e73 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b3e74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b3e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e85 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b3e19 X0 X0
               have i₂ := b3e74 (σ X0)
               grind)
            | exact superpose b3e74 b3e19
            | exact resolve b3e19 b3e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b3e85 X0
               have i₂ := b3e74 X0
               grind)
            | exact superpose b3e74 b3e85
            | exact resolve b3e85 b3e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e74 b3e85
          have b3e94 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ x)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e100 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b3e94
          have b3e103 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e100
               have r₂ := b3e25
               grind)
            | exact resolve b3e100 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e100
          have b3e108 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e103
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e103
            | exact resolve b3e103 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e103
          have b3e190 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b3e14 (k x y)
               have i₂ := b3e108
               grind)
            | exact superpose b3e108 b3e14
            | exact resolve b3e14 b3e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e108
          have b3e191 : x = (k x y) := by
            first
            | (have i₁ := b3e190
               have i₂ := b3e14 x
               grind)
            | exact superpose b3e14 b3e190
            | exact resolve b3e190 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e190
          have b3e303 : (M.op x x) = (k x y) := by
            first
            | (have j0 := b3e73 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e73
          have b3e306 : x = (M.op x x) := by
            first
            | (have i₁ := b3e303
               have i₂ := b3e191
               grind)
            | exact superpose b3e191 b3e303
            | exact resolve b3e303 b3e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e191 b3e303
          have b3e319 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b3e37 x x x
               have i₂ := b3e306
               grind)
            | exact superpose b3e306 b3e37
            | exact resolve b3e37 b3e306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e37
          have b3e1404 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b3e25
               have i₂ := b3e88 y
               grind)
            | exact superpose b3e88 b3e25
            | exact resolve b3e25 b3e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25
          have b3e1432 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b3e1404
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e1404
            | exact resolve b3e1404 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1404
          have b3e1439 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e1432
               have i₂ := b3e319 y
               grind)
            | exact superpose b3e319 b3e1432
            | exact resolve b3e1432 b3e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e319 b3e1432
          have b3e1442 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e1439
               have i₂ := b3e88 x
               grind)
            | exact superpose b3e88 b3e1439
            | exact resolve b3e1439 b3e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e88 b3e1439
          have b3e1443 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e1442
               have i₂ := b3e306
               grind)
            | exact superpose b3e306 b3e1442
            | exact resolve b3e1442 b3e306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e306 b3e1442
          have b3e1444 : False := by grind
          exact b3e1444
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : (M.op y x) = (M.op y y) := by grind
            have b4e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
            have b4e25 : (M.op x y) ≠ (M.op x x) := by grind
            have b4e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e25
              | exact resolve b4e25 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b4e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b4e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b4e14 b4e14
              | exact resolve b4e14 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b4e34 X0 X1 x X3
                 have i₂ := b4e14 X0 X1 x
                 grind)
              | exact superpose b4e14 b4e34
              | exact resolve b4e34 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e34
            have b4e67 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b4e17 (σ x) (σ x)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e17
              | exact resolve b4e17 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e68 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b4e17 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 y y
                 grind)
              | (have r₁ := b4e17 x y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b4e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e73 : (M.op x x) = (k x y) := by grind
            clear b4e68
            have b4e74 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
            clear b4e67
            have b4e76 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
              first
              | (have i₁ := b4e74
                 have i₂ := b4e20 x x
                 grind)
              | exact superpose b4e20 b4e74
              | exact resolve b4e74 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e74
            have b4e80 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b4e76
                 have i₂ := b4e72 x
                 grind)
              | exact superpose b4e72 b4e76
              | exact resolve b4e76 b4e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e76
            have b4e83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b4e20 X0 X0
                 have i₂ := b4e72 (σ X0)
                 grind)
              | exact superpose b4e72 b4e20
              | exact resolve b4e20 b4e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b4e83 X0
                 have i₂ := b4e72 X0
                 grind)
              | exact superpose b4e72 b4e83
              | exact resolve b4e83 b4e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e72 b4e83
            have b4e93 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (σ x) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b4e18 (σ x) X0
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) X0
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e96 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (σ x) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b4e93 X0
                 have i₂ := b4e80
                 grind)
              | exact superpose b4e80 b4e93
              | (have j0 := b4e93 X0
                 grind)
              | exact resolve b4e93 b4e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e93
            have b4e224 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e80
                 grind)
              | exact superpose b4e80 b4e23
              | exact resolve b4e23 b4e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e232 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b4e224
                 have i₂ := b4e84 y
                 grind)
              | exact superpose b4e84 b4e224
              | exact resolve b4e224 b4e84
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e224
            have b4e632 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e96 (σ y)
                 have i₂ := b4e80
                 grind)
              | exact superpose b4e80 b4e96
              | (have j0 := b4e96 (σ y)
                 grind)
              | (have r₁ := b4e96 (σ y)
                 have r₂ := b4e80
                 grind)
              | exact resolve b4e96 b4e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e80 b4e96
            have b4e633 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b4e632
            have b4e634 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e633
                 have i₂ := b4e84 y
                 grind)
              | exact superpose b4e84 b4e633
              | exact resolve b4e633 b4e84
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e84 b4e633
            have b4e635 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e634
                 have r₂ := b4e232
                 grind)
              | exact resolve b4e634 b4e232
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e232 b4e634
            have b4e636 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b4e635
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e635
              | exact resolve b4e635 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e635
            have b4e637 : (σ x) = (σ (M.op x x)) := by
              first
              | (have i₁ := b4e636
                 have i₂ := b4e73
                 grind)
              | exact superpose b4e73 b4e636
              | exact resolve b4e636 b4e73
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e73 b4e636
            have b4e645 : (M.op x x) = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 (M.op x x)
                 have i₂ := b4e637
                 grind)
              | exact superpose b4e637 b4e15
              | exact resolve b4e15 b4e637
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e637
            have b4e646 : x = (M.op x x) := by
              first
              | (have i₁ := b4e645
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e645
              | exact resolve b4e645 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e645
            have b4e759 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b4e27
                 have i₂ := b4e646
                 grind)
              | exact superpose b4e646 b4e27
              | exact resolve b4e27 b4e646
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e27
            have b4e768 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b4e35 x x x
                 have i₂ := b4e646
                 grind)
              | exact superpose b4e646 b4e35
              | exact resolve b4e35 b4e646
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e35 b4e646
            have b4e956 : x = (M.op y y) := by
              first
              | (have i₁ := b4e22
                 have i₂ := b4e768 y
                 grind)
              | exact superpose b4e768 b4e22
              | exact resolve b4e22 b4e768
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e768
            have b4e958 : False := by grind
            exact b4e958
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : (M.op y x) = (M.op y y) := by grind
            have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b5e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
            have b5e25 : (M.op x y) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b5e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b5e31 X0 X1 x X3
                 have i₂ := b5e14 X0 X1 x
                 grind)
              | exact superpose b5e14 b5e31
              | exact resolve b5e31 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31
            have b5e38 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 X1 x
                 have i₂ := b5e32 (M.op X0 X1) X1 x
                 grind)
              | exact superpose b5e32 b5e14
              | exact resolve b5e14 b5e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e62 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b5e17 (σ x) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e17
              | exact resolve b5e17 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e63 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b5e17 x y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e17
              | (have j0 := b5e17 y y
                 grind)
              | (have r₁ := b5e17 x y
                 have r₂ := b5e22
                 grind)
              | exact resolve b5e17 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b5e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e68 : (M.op x x) = (k x y) := by grind
            clear b5e63
            have b5e69 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
            clear b5e62
            have b5e71 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
              first
              | (have i₁ := b5e69
                 have i₂ := b5e20 x x
                 grind)
              | exact superpose b5e20 b5e69
              | exact resolve b5e69 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e69
            have b5e75 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b5e71
                 have i₂ := b5e67 x
                 grind)
              | exact superpose b5e67 b5e71
              | exact resolve b5e71 b5e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e71
            have b5e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b5e20 X0 X0
                 have i₂ := b5e67 (σ X0)
                 grind)
              | exact superpose b5e67 b5e20
              | exact resolve b5e20 b5e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b5e78 X0
                 have i₂ := b5e67 X0
                 grind)
              | exact superpose b5e67 b5e78
              | exact resolve b5e78 b5e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e67 b5e78
            have b5e87 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (σ x) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b5e18 (σ x) X0
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e18
              | (have j0 := b5e18 (σ x) X0
                 grind)
              | (have r₁ := b5e18 (σ x) (σ y)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e18 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e89 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (σ x) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b5e87 X0
                 have i₂ := b5e75
                 grind)
              | exact superpose b5e75 b5e87
              | (have j0 := b5e87 X0
                 grind)
              | exact resolve b5e87 b5e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e87
            have b5e213 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e75
                 grind)
              | exact superpose b5e75 b5e23
              | exact resolve b5e23 b5e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e221 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b5e213
                 have i₂ := b5e79 y
                 grind)
              | exact superpose b5e79 b5e213
              | exact resolve b5e213 b5e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e213
            have b5e643 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b5e89 (σ y)
                 have i₂ := b5e75
                 grind)
              | exact superpose b5e75 b5e89
              | (have j0 := b5e89 (σ y)
                 grind)
              | (have r₁ := b5e89 (σ y)
                 have r₂ := b5e75
                 grind)
              | exact resolve b5e89 b5e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e75 b5e89
            have b5e644 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b5e643
            have b5e645 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b5e644
                 have i₂ := b5e79 y
                 grind)
              | exact superpose b5e79 b5e644
              | exact resolve b5e644 b5e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e79 b5e644
            have b5e646 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e645
                 have r₂ := b5e221
                 grind)
              | exact resolve b5e645 b5e221
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e221 b5e645
            have b5e647 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e646
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e646
              | exact resolve b5e646 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e646
            have b5e648 : (σ x) = (σ (M.op x x)) := by
              first
              | (have i₁ := b5e647
                 have i₂ := b5e68
                 grind)
              | exact superpose b5e68 b5e647
              | exact resolve b5e647 b5e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e68 b5e647
            have b5e656 : (M.op x x) = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 (M.op x x)
                 have i₂ := b5e648
                 grind)
              | exact superpose b5e648 b5e15
              | exact resolve b5e15 b5e648
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e648
            have b5e657 : x = (M.op x x) := by
              first
              | (have i₁ := b5e656
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e656
              | exact resolve b5e656 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e656
            have b5e774 : x ≠ (M.op x y) := by
              first
              | (have i₁ := b5e25
                 have i₂ := b5e657
                 grind)
              | exact superpose b5e657 b5e25
              | exact resolve b5e25 b5e657
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e783 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b5e32 x x x
                 have i₂ := b5e657
                 grind)
              | exact superpose b5e657 b5e32
              | exact resolve b5e32 b5e657
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e32 b5e657
            have b5e958 : x = (M.op y y) := by
              first
              | (have i₁ := b5e22
                 have i₂ := b5e783 y
                 grind)
              | exact superpose b5e783 b5e22
              | exact resolve b5e22 b5e783
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e783
            have b5e1543 : x = (M.op x y) := by
              first
              | (have i₁ := b5e38 y y
                 have i₂ := b5e958
                 grind)
              | exact superpose b5e958 b5e38
              | exact resolve b5e38 b5e958
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e38 b5e958
            have b5e1550 : False := by grind
            exact b5e1550
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : (M.op y x) = (M.op y y) := by grind
          have b6e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e67 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b6e16 X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b6e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e81 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e19 X0 X0
               have i₂ := b6e70 (σ X0)
               grind)
            | exact superpose b6e70 b6e19
            | exact resolve b6e19 b6e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b6e81 X0
               have i₂ := b6e70 X0
               grind)
            | exact superpose b6e70 b6e81
            | exact resolve b6e81 b6e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e70 b6e81
          have b6e133 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e22
               have i₂ := b6e18 X0 (σ y)
               grind)
            | (have i₁ := b6e22
               have i₂ := b6e18 (σ y) (σ y)
               grind)
            | exact superpose b6e18 b6e22
            | (have j1 := b6e18 X0 (σ y)
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e22 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e318 : (M.op x x) = (k x y) := by
            first
            | (have j0 := b6e67 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e67
          have b6e666 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b6e133 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e133
          have b6e667 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e666
               have r₂ := b6e23
               grind)
            | exact resolve b6e666 b6e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e666
          have b6e668 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e667
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e667
            | exact resolve b6e667 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e667
          have b6e669 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b6e668
               have i₂ := b6e318
               grind)
            | exact superpose b6e318 b6e668
            | exact resolve b6e668 b6e318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e318 b6e668
          have b6e672 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e669
               grind)
            | exact superpose b6e669 b6e23
            | exact resolve b6e23 b6e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e669
          have b6e682 : False := by grind
          exact b6e682
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : (M.op y x) = (M.op y y) := by grind
            have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e64 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 y y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b7e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e68 : (M.op x x) = (k x y) := by grind
            clear b7e64
            have b7e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b7e20 X0 X0
                 have i₂ := b7e67 (σ X0)
                 grind)
              | exact superpose b7e67 b7e20
              | exact resolve b7e20 b7e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b7e75 X0
                 have i₂ := b7e67 X0
                 grind)
              | exact superpose b7e67 b7e75
              | exact resolve b7e75 b7e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e67 b7e75
            have b7e142 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) (σ x)
                 grind)
              | exact superpose b7e19 b7e24
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e24
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e24 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e212 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b7e24
                 have i₂ := b7e76 x
                 grind)
              | exact superpose b7e76 b7e24
              | exact resolve b7e24 b7e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e76
            have b7e577 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b7e142 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e142
            have b7e578 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e577
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e577 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e577
            have b7e579 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e578
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e578
              | exact resolve b7e578 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e578
            have b7e580 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b7e579
                 have i₂ := b7e68
                 grind)
              | exact superpose b7e68 b7e579
              | exact resolve b7e579 b7e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e68 b7e579
            have b7e581 : False := by grind
            exact b7e581
          · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : (M.op y x) = (M.op y y) := by grind
            have b8e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b8e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e57 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 y y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b8e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e63 : (M.op x x) = (k x y) := by grind
            clear b8e57
            have b8e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b8e20 X0 X0
                 have i₂ := b8e62 (σ X0)
                 grind)
              | exact superpose b8e62 b8e20
              | exact resolve b8e20 b8e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b8e70 X0
                 have i₂ := b8e62 X0
                 grind)
              | exact superpose b8e62 b8e70
              | exact resolve b8e70 b8e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e62 b8e70
            have b8e134 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b8e24
                 have i₂ := b8e19 (σ x) X0
                 grind)
              | (have i₁ := b8e24
                 have i₂ := b8e19 (σ x) (σ x)
                 grind)
              | exact superpose b8e19 b8e24
              | (have j1 := b8e19 (σ x) X0
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e24 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e236 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b8e24
                 have i₂ := b8e71 x
                 grind)
              | exact superpose b8e71 b8e24
              | exact resolve b8e24 b8e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e71
            have b8e533 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b8e134 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e134
            have b8e534 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e533
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e533 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e533
            have b8e535 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e534
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e534
              | exact resolve b8e534 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e534
            have b8e536 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b8e535
                 have i₂ := b8e63
                 grind)
              | exact superpose b8e63 b8e535
              | exact resolve b8e535 b8e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e63 b8e535
            have b8e537 : False := by grind
            exact b8e537
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b9e22 : (M.op y x) = (M.op x x) := by grind
          have b9e23 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b9e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b9e32 X0 X1 x X3
               have i₂ := b9e13 X0 X1 x
               grind)
            | exact superpose b9e13 b9e32
            | exact resolve b9e32 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e63 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ y) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e67 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 X0 (σ y)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e70 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b9e63
          have b9e72 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b9e70
               have i₂ := b9e19 y y
               grind)
            | exact superpose b9e19 b9e70
            | exact resolve b9e70 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e70
          have b9e76 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b9e72
               have i₂ := b9e68 y
               grind)
            | exact superpose b9e68 b9e72
            | exact resolve b9e72 b9e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e72
          have b9e79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 X0
               have i₂ := b9e68 (σ X0)
               grind)
            | exact superpose b9e68 b9e19
            | exact resolve b9e19 b9e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b9e79 X0
               have i₂ := b9e68 X0
               grind)
            | exact superpose b9e68 b9e79
            | exact resolve b9e79 b9e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e68 b9e79
          have b9e85 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ x = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x x
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e90 : (M.op y y) = (M.op x x) ∨ x = (k x y) := by grind
          clear b9e85
          have b9e94 : x = (k x y) := by
            first
            | (have r₁ := b9e90
               have r₂ := b9e25
               grind)
            | exact resolve b9e90 b9e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e90
          have b9e239 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b9e33 (σ X0) (σ X0) x
               have i₂ := b9e80 X0
               grind)
            | exact superpose b9e80 b9e33
            | exact resolve b9e33 b9e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e33
          have b9e332 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b9e67 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e67
          have b9e335 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e332
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e332
            | exact resolve b9e332 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e332
          have b9e345 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e335
               have i₂ := b9e94
               grind)
            | exact superpose b9e94 b9e335
            | exact resolve b9e335 b9e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e94 b9e335
          have b9e355 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b9e345
               have i₂ := b9e80 x
               grind)
            | exact superpose b9e80 b9e345
            | exact resolve b9e345 b9e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e80 b9e345
          have b9e365 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 (M.op x x)
               have i₂ := b9e355
               grind)
            | exact superpose b9e355 b9e14
            | exact resolve b9e14 b9e355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e366 : x = (M.op x x) := by
            first
            | (have i₁ := b9e365
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e365
            | exact resolve b9e365 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e365
          have b9e3116 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b9e239 x x
               have i₂ := b9e355
               grind)
            | exact superpose b9e355 b9e239
            | exact resolve b9e239 b9e355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e239 b9e355
          have b9e3930 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b9e76
               have i₂ := b9e3116 (σ y)
               grind)
            | exact superpose b9e3116 b9e76
            | exact resolve b9e76 b9e3116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e76 b9e3116
          have b9e4085 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 (M.op y y)
               have i₂ := b9e3930
               grind)
            | exact superpose b9e3930 b9e14
            | exact resolve b9e14 b9e3930
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3930
          have b9e4112 : x = (M.op y y) := by
            first
            | (have i₁ := b9e4085
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e4085
            | exact resolve b9e4085 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e4085
          have b9e4259 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b9e25
               have i₂ := b9e4112
               grind)
            | exact superpose b9e4112 b9e25
            | exact resolve b9e25 b9e4112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e25 b9e4112
          have b9e4282 : False := by grind
          exact b9e4282
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b10e23 : (M.op y x) = (M.op x x) := by grind
            have b10e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b10e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b10e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b10e35 X0 X1 x X3
                 have i₂ := b10e14 X0 X1 x
                 grind)
              | exact superpose b10e14 b10e35
              | exact resolve b10e35 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e49 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ x))) := by
              intro X0
              first
              | (have i₁ := b10e14 (σ y) (σ x) x
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e14
              | exact resolve b10e14 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e50 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
              first
              | (have i₁ := b10e49 x
                 have i₂ := b10e36 (M.op (σ y) (σ y)) (σ x) x
                 grind)
              | exact superpose b10e36 b10e49
              | exact resolve b10e49 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e49
            have b10e65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e17 (M.op X0 X1) X2
                 have i₂ := b10e36 X0 X1 X2
                 grind)
              | exact superpose b10e36 b10e17
              | (have j0 := b10e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b10e17 (M.op X1 X1) X1
                 have r₂ := b10e36 X1 X1 X1
                 grind)
              | exact resolve b10e17 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e66 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b10e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e73 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b10e66
            have b10e76 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b10e73
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e73
              | exact resolve b10e73 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e73
            have b10e77 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) ≠ (M.op X2 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e65 X0 X1 X2
                 have i₂ := b10e36 X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b10e36 b10e65
              | (have j0 := b10e65 X0 X1 X2
                 grind)
              | (have r₁ := b10e65 X0 X1 (M.op X0 X1)
                 have r₂ := b10e36 X0 X1 (M.op X0 X1)
                 grind)
              | (have r₁ := b10e65 x (M.op X1 X1) X1
                 have r₂ := b10e36 X1 X1 x
                 grind)
              | exact resolve b10e65 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e65
            have b10e82 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b10e20 X0 X0
                 have i₂ := b10e71 (σ X0)
                 grind)
              | exact superpose b10e71 b10e20
              | exact resolve b10e20 b10e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b10e82 X0
                 have i₂ := b10e71 X0
                 grind)
              | exact superpose b10e71 b10e82
              | exact resolve b10e82 b10e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e82
            have b10e86 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e18 (M.op X0 X1) x
                 have i₂ := b10e36 X0 X1 x
                 grind)
              | exact superpose b10e36 b10e18
              | (have j0 := b10e18 (M.op X0 X1) X2
                 grind)
              | exact resolve b10e18 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e91 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = (k x X0) := by
              intro X0
              first
              | (have i₁ := b10e18 x X0
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e18
              | (have j0 := b10e18 x X0
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e23
                 grind)
              | exact resolve b10e18 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e97 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b10e86 X0 X1 X2
                 have j1 := b10e77 X0 X1 X2
                 grind)
              | (have r₁ := b10e86 X0 X1 X2
                 have r₂ := b10e77 X0 X1 X2
                 grind)
              | (have r₁ := b10e86 X2 X2 X1
                 have r₂ := b10e77 X1 X1 X2
                 grind)
              | exact resolve b10e86 b10e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e77 b10e86
            have b10e102 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b10e97 X0 X1 X2
                 grind)
              | (have r₁ := b10e97 X0 X1 X2
                 have r₂ := b10e36 X0 X1 (M.op X0 X1)
                 grind)
              | exact resolve b10e97 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e97
            have b10e216 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ x)
                 have i₂ := b10e76
                 grind)
              | exact superpose b10e76 b10e17
              | exact resolve b10e17 b10e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e217 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b10e36 (σ x) (σ x) x
                 have i₂ := b10e76
                 grind)
              | exact superpose b10e76 b10e36
              | exact resolve b10e36 b10e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36 b10e76
            have b10e220 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
            clear b10e216
            have b10e221 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b10e220
                 have i₂ := b10e20 x x
                 grind)
              | exact superpose b10e20 b10e220
              | exact resolve b10e220 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e220
            have b10e223 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b10e221
                 have i₂ := b10e71 x
                 grind)
              | exact superpose b10e71 b10e221
              | exact resolve b10e221 b10e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e71 b10e221
            have b10e224 : (σ (k x y)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b10e223
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e223
              | exact resolve b10e223 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e223
            have b10e227 : (k x y) = (τ (σ (M.op y x))) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e224
                 grind)
              | exact superpose b10e224 b10e15
              | exact resolve b10e15 b10e224
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e224
            have b10e228 : (M.op y x) = (k x y) := by
              first
              | (have i₁ := b10e227
                 have i₂ := b10e15 (M.op y x)
                 grind)
              | exact superpose b10e15 b10e227
              | exact resolve b10e227 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e227
            have b10e278 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by
              first
              | (have j0 := b10e91 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e91
            have b10e279 : x = (k x y) := by
              first
              | (have r₁ := b10e278
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e278 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e278
            have b10e282 : x = (M.op y x) := by
              first
              | (have i₁ := b10e228
                 have i₂ := b10e279
                 grind)
              | exact superpose b10e279 b10e228
              | exact resolve b10e228 b10e279
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e228 b10e279
            have b10e345 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b10e22
                 have i₂ := b10e282
                 grind)
              | exact superpose b10e282 b10e22
              | exact resolve b10e22 b10e282
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e351 : ∀ X0 : G, x = (k x X0) := by
              intro X0
              first
              | (have i₁ := b10e102 y x x
                 have i₂ := b10e282
                 grind)
              | exact superpose b10e282 b10e102
              | exact resolve b10e102 b10e282
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e102 b10e282
            have b10e2909 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b10e217 X0
                 have i₂ := b10e351 y
                 grind)
              | exact superpose b10e351 b10e217
              | exact resolve b10e217 b10e351
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e217 b10e351
            have b10e3216 : (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b10e50
                 have i₂ := b10e2909 (M.op (σ y) (σ y))
                 grind)
              | exact superpose b10e2909 b10e50
              | exact resolve b10e50 b10e2909
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e50 b10e2909
            have b10e3276 : (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b10e3216
                 have i₂ := b10e83 y
                 grind)
              | exact superpose b10e83 b10e3216
              | exact resolve b10e3216 b10e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e83 b10e3216
            have b10e3411 : (M.op y y) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (M.op y y)
                 have i₂ := b10e3276
                 grind)
              | exact superpose b10e3276 b10e15
              | exact resolve b10e15 b10e3276
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e3276
            have b10e3438 : x = (M.op y y) := by
              first
              | (have i₁ := b10e3411
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e3411
              | exact resolve b10e3411 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e3411
            have b10e3449 : False := by grind
            exact b10e3449
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b11e23 : (M.op y x) = (M.op x x) := by grind
            have b11e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b11e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b11e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b11e32 X0 X1 x X3
                 have i₂ := b11e14 X0 X1 x
                 grind)
              | exact superpose b11e14 b11e32
              | exact resolve b11e32 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e45 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ x))) := by
              intro X0
              first
              | (have i₁ := b11e14 (σ y) (σ x) x
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e14
              | exact resolve b11e14 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e46 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
              first
              | (have i₁ := b11e45 x
                 have i₂ := b11e33 (M.op (σ y) (σ y)) (σ x) x
                 grind)
              | exact superpose b11e33 b11e45
              | exact resolve b11e45 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e45
            have b11e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e17 (M.op X0 X1) X2
                 have i₂ := b11e33 X0 X1 X2
                 grind)
              | exact superpose b11e33 b11e17
              | (have j0 := b11e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b11e17 (M.op X1 X1) X1
                 have r₂ := b11e33 X1 X1 X1
                 grind)
              | exact resolve b11e17 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e61 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b11e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e68 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b11e61
            have b11e71 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b11e68
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e68
              | exact resolve b11e68 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e68
            have b11e72 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) ≠ (M.op X2 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e60 X0 X1 X2
                 have i₂ := b11e33 X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b11e33 b11e60
              | (have j0 := b11e60 X0 X1 X2
                 grind)
              | (have r₁ := b11e60 X0 X1 (M.op X0 X1)
                 have r₂ := b11e33 X0 X1 (M.op X0 X1)
                 grind)
              | (have r₁ := b11e60 x (M.op X1 X1) X1
                 have r₂ := b11e33 X1 X1 x
                 grind)
              | exact resolve b11e60 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b11e20 X0 X0
                 have i₂ := b11e66 (σ X0)
                 grind)
              | exact superpose b11e66 b11e20
              | exact resolve b11e20 b11e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b11e77 X0
                 have i₂ := b11e66 X0
                 grind)
              | exact superpose b11e66 b11e77
              | exact resolve b11e77 b11e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e77
            have b11e81 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e18 (M.op X0 X1) x
                 have i₂ := b11e33 X0 X1 x
                 grind)
              | exact superpose b11e33 b11e18
              | (have j0 := b11e18 (M.op X0 X1) X2
                 grind)
              | exact resolve b11e18 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e85 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ x = (k x X0) := by
              intro X0
              first
              | (have i₁ := b11e18 x X0
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x X0
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e89 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b11e81 X0 X1 X2
                 have j1 := b11e72 X0 X1 X2
                 grind)
              | (have r₁ := b11e81 X0 X1 X2
                 have r₂ := b11e72 X0 X1 X2
                 grind)
              | (have r₁ := b11e81 X2 X2 X1
                 have r₂ := b11e72 X1 X1 X2
                 grind)
              | exact resolve b11e81 b11e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e72 b11e81
            have b11e93 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b11e89 X0 X1 X2
                 grind)
              | (have r₁ := b11e89 X0 X1 X2
                 have r₂ := b11e33 X0 X1 (M.op X0 X1)
                 grind)
              | exact resolve b11e89 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e89
            have b11e204 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ x)
                 have i₂ := b11e71
                 grind)
              | exact superpose b11e71 b11e17
              | exact resolve b11e17 b11e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e205 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (σ (k x y))) := by
              intro X0
              first
              | (have i₁ := b11e33 (σ x) (σ x) x
                 have i₂ := b11e71
                 grind)
              | exact superpose b11e71 b11e33
              | exact resolve b11e33 b11e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33 b11e71
            have b11e208 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
            clear b11e204
            have b11e209 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b11e208
                 have i₂ := b11e20 x x
                 grind)
              | exact superpose b11e20 b11e208
              | exact resolve b11e208 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e208
            have b11e211 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b11e209
                 have i₂ := b11e66 x
                 grind)
              | exact superpose b11e66 b11e209
              | exact resolve b11e209 b11e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e66 b11e209
            have b11e212 : (σ (k x y)) = (σ (M.op y x)) := by
              first
              | (have i₁ := b11e211
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e211
              | exact resolve b11e211 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e211
            have b11e223 : (k x y) = (τ (σ (M.op y x))) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e212
                 grind)
              | exact superpose b11e212 b11e15
              | exact resolve b11e15 b11e212
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e212
            have b11e224 : (M.op y x) = (k x y) := by
              first
              | (have i₁ := b11e223
                 have i₂ := b11e15 (M.op y x)
                 grind)
              | exact superpose b11e15 b11e223
              | exact resolve b11e223 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e223
            have b11e239 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by
              first
              | (have j0 := b11e85 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e85
            have b11e240 : x = (k x y) := by
              first
              | (have r₁ := b11e239
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e239 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e239
            have b11e243 : x = (M.op y x) := by
              first
              | (have i₁ := b11e224
                 have i₂ := b11e240
                 grind)
              | exact superpose b11e240 b11e224
              | exact resolve b11e224 b11e240
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e224 b11e240
            have b11e302 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e243
                 grind)
              | exact superpose b11e243 b11e22
              | exact resolve b11e22 b11e243
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e308 : ∀ X0 : G, x = (k x X0) := by
              intro X0
              first
              | (have i₁ := b11e93 y x x
                 have i₂ := b11e243
                 grind)
              | exact superpose b11e243 b11e93
              | exact resolve b11e93 b11e243
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e93 b11e243
            have b11e2750 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b11e205 X0
                 have i₂ := b11e308 y
                 grind)
              | exact superpose b11e308 b11e205
              | exact resolve b11e205 b11e308
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e205 b11e308
            have b11e3057 : (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b11e46
                 have i₂ := b11e2750 (M.op (σ y) (σ y))
                 grind)
              | exact superpose b11e2750 b11e46
              | exact resolve b11e46 b11e2750
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e46 b11e2750
            have b11e3117 : (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b11e3057
                 have i₂ := b11e78 y
                 grind)
              | exact superpose b11e78 b11e3057
              | exact resolve b11e3057 b11e78
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e78 b11e3057
            have b11e3250 : (M.op y y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (M.op y y)
                 have i₂ := b11e3117
                 grind)
              | exact superpose b11e3117 b11e15
              | exact resolve b11e15 b11e3117
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e3117
            have b11e3277 : x = (M.op y y) := by
              first
              | (have i₁ := b11e3250
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e3250
              | exact resolve b11e3250 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e3250
            have b11e3288 : False := by grind
            exact b11e3288
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b12e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b12e23 : (M.op y x) = (M.op x x) := by grind
            have b12e26 : (M.op x y) = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e22
              | exact resolve b12e22 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b12e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e35 X0 X1 x X3
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e35
              | exact resolve b12e35 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e35
            have b12e68 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by
              first
              | (have i₁ := b12e17 y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e17
              | (have j0 := b12e17 x x
                 grind)
              | (have r₁ := b12e17 y x
                 have r₂ := b12e26
                 grind)
              | exact resolve b12e17 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b12e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e72 : (M.op y y) = (k y x) := by grind
            clear b12e68
            have b12e79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b12e20 X0 X0
                 have i₂ := b12e71 (σ X0)
                 grind)
              | exact superpose b12e71 b12e20
              | exact resolve b12e20 b12e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b12e79 X0
                 have i₂ := b12e71 X0
                 grind)
              | exact superpose b12e71 b12e79
              | exact resolve b12e79 b12e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e71 b12e79
            have b12e137 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e18 X0 X1
                 have i₂ := b12e19 X0 X1
                 grind)
              | (have i₁ := b12e18 X0 X0
                 have i₂ := b12e19 X0 X1
                 grind)
              | exact superpose b12e19 b12e18
              | (have j0 := b12e18 X0 X1
                 have j1 := b12e19 X0 X1
                 grind)
              | (have r₁ := b12e18 X1 X1
                 have r₂ := b12e19 X1 X1
                 grind)
              | (have r₁ := b12e18 X0 X0
                 have r₂ := b12e19 X0 X0
                 grind)
              | (have r₁ := b12e18 X0 X1
                 have r₂ := b12e19 X0 X1
                 grind)
              | exact resolve b12e18 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e151 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X1 X0
                 have i₂ := b12e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b12e19 b12e20
              | (have j1 := b12e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b12e20 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e154 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
              intro X0 X1
              first
              | (have j0 := b12e19 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e156 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b12e137 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e137
            have b12e159 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e151 X0 X1
                 have i₂ := b12e80 X0
                 grind)
              | exact superpose b12e80 b12e151
              | (have j0 := b12e151 X0 X1
                 grind)
              | exact resolve b12e151 b12e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e151
            have b12e162 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              first
              | (have j0 := b12e156 X0 X1
                 have j1 := b12e154 X1 X0
                 grind)
              | (have r₁ := b12e156 X0 X1
                 have r₂ := b12e154 X0 X1
                 grind)
              | (have r₁ := b12e156 X1 X0
                 have r₂ := b12e154 X0 X1
                 grind)
              | (have r₁ := b12e156 X0 X0
                 have r₂ := b12e154 X0 X0
                 grind)
              | exact resolve b12e156 b12e154
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e154 b12e156
            have b12e173 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b12e159 X0 X1
                 have i₂ := b12e80 X1
                 grind)
              | exact superpose b12e80 b12e159
              | (have j0 := b12e159 X0 X1
                 grind)
              | exact resolve b12e159 b12e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e159
            have b12e273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e162 (σ X0) (σ X1)
                 have i₂ := b12e20 X0 X1
                 grind)
              | exact superpose b12e20 b12e162
              | (have j0 := b12e162 (σ X0) (σ X1)
                 grind)
              | exact resolve b12e162 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e162
            have b12e329 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e273 X0 X1
                 have i₂ := b12e80 X1
                 grind)
              | exact superpose b12e80 b12e273
              | (have j0 := b12e273 X0 X1
                 grind)
              | exact resolve b12e273 b12e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e273
            have b12e1142 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b12e173 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e173
            have b12e10286 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e18 (σ X0) (σ X1)
                 have i₂ := b12e329 X0 X1
                 grind)
              | exact superpose b12e329 b12e18
              | (have j0 := b12e18 (σ X0) (σ X1)
                 have j1 := b12e329 X0 X1
                 grind)
              | exact resolve b12e18 b12e329
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e10434 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b12e329 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e10507 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e10286 X0 X1
                 have i₂ := b12e80 X0
                 grind)
              | exact superpose b12e80 b12e10286
              | (have j0 := b12e10286 X0 X1
                 grind)
              | exact resolve b12e10286 b12e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e10286
            have b12e10623 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e10507 X0 X1
                 have i₂ := b12e80 X1
                 grind)
              | exact superpose b12e80 b12e10507
              | (have j0 := b12e10507 X0 X1
                 grind)
              | exact resolve b12e10507 b12e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e80 b12e10507
            have b12e10697 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have j0 := b12e10623 X0 X1
                 have j1 := b12e10434 X1 X0
                 grind)
              | (have r₁ := b12e10623 X1 X0
                 have r₂ := b12e10434 X0 X1
                 grind)
              | (have r₁ := b12e10623 (M.op X0 X0) X0
                 have r₂ := b12e10434 X0 (M.op X0 X0)
                 grind)
              | exact resolve b12e10623 b12e10434
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e10434 b12e10623
            have b12e10742 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e10697 X0 X1
                 have i₂ := b12e20 X0 X1
                 grind)
              | exact superpose b12e20 b12e10697
              | (have j0 := b12e10697 X0 X1
                 grind)
              | exact resolve b12e10697 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e10697
            have b12e10743 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
              intro X0 X1
              first
              | (have j0 := b12e10742 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e10742
            have b12e20623 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b12e1142 x y
                 have i₂ := b12e72
                 grind)
              | exact superpose b12e72 b12e1142
              | (have j0 := b12e1142 x y
                 grind)
              | exact resolve b12e1142 b12e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1142
            have b12e20684 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
            clear b12e20623
            have b12e20729 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
              first
              | (have r₁ := b12e20684
                 have r₂ := b12e29
                 grind)
              | exact resolve b12e20684 b12e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e20684
            have b12e20902 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b12e20729
                 have i₂ := b12e329 y x
                 grind)
              | exact superpose b12e329 b12e20729
              | (have j1 := b12e329 y x
                 grind)
              | exact resolve b12e20729 b12e329
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e329 b12e20729
            have b12e20990 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have j1 := b12e10743 y x
                 grind)
              | (have r₁ := b12e20902
                 have r₂ := b12e10743 y x
                 grind)
              | exact resolve b12e20902 b12e10743
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e10743 b12e20902
            have b12e21000 : (σ y) = (σ (k y x)) := by
              first
              | (have r₁ := b12e20990
                 have r₂ := b12e29
                 grind)
              | exact resolve b12e20990 b12e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29 b12e20990
            have b12e21004 : (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b12e21000
                 have i₂ := b12e72
                 grind)
              | exact superpose b12e72 b12e21000
              | exact resolve b12e21000 b12e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e72 b12e21000
            have b12e21240 : (M.op y y) = (τ (σ y)) := by
              first
              | (have i₁ := b12e15 (M.op y y)
                 have i₂ := b12e21004
                 grind)
              | exact superpose b12e21004 b12e15
              | exact resolve b12e15 b12e21004
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e21004
            have b12e21316 : y = (M.op y y) := by
              first
              | (have i₁ := b12e21240
                 have i₂ := b12e15 y
                 grind)
              | exact superpose b12e15 b12e21240
              | exact resolve b12e21240 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e21240
            have b12e21590 : y ≠ (M.op x x) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e21316
                 grind)
              | exact superpose b12e21316 b12e28
              | exact resolve b12e28 b12e21316
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28
            have b12e21629 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b12e36 y y x
                 have i₂ := b12e21316
                 grind)
              | exact superpose b12e21316 b12e36
              | exact resolve b12e36 b12e21316
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36 b12e21316
            have b12e22335 : y = (M.op x x) := by
              first
              | (have i₁ := b12e26
                 have i₂ := b12e21629 x
                 grind)
              | exact superpose b12e21629 b12e26
              | exact resolve b12e26 b12e21629
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e21629
            have b12e22343 : False := by grind
            exact b12e22343
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b13e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b13e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b13e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b13e37 X0 X1 x X3
                   have i₂ := b13e15 X0 X1 x
                   grind)
                | exact superpose b13e15 b13e37
                | exact resolve b13e37 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e37
              have b13e45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 X1 x
                   have i₂ := b13e38 (M.op X0 X1) X1 x
                   grind)
                | exact superpose b13e38 b13e15
                | exact resolve b13e15 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b13e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e84 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b13e21 X0 X0
                   have i₂ := b13e75 (σ X0)
                   grind)
                | exact superpose b13e75 b13e21
                | exact resolve b13e21 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e84 X0
                   have i₂ := b13e75 X0
                   grind)
                | exact superpose b13e75 b13e84
                | exact resolve b13e84 b13e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e75 b13e84
              have b13e97 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ y = (k y X0) := by
                intro X0
                first
                | (have i₁ := b13e19 y X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 y X0
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e160 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 X1 X0
                   have i₂ := b13e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b13e20 b13e21
                | (have j1 := b13e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b13e21 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e169 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e160 X0 X1
                   have i₂ := b13e87 X0
                   grind)
                | exact superpose b13e87 b13e160
                | (have j0 := b13e160 X0 X1
                   grind)
                | exact resolve b13e160 b13e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e160
              have b13e182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e169 X0 X1
                   have i₂ := b13e87 X1
                   grind)
                | exact superpose b13e87 b13e169
                | (have j0 := b13e169 X0 X1
                   grind)
                | exact resolve b13e169 b13e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e169
              have b13e248 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b13e38 (σ X0) (σ X0) x
                   have i₂ := b13e87 X0
                   grind)
                | exact superpose b13e87 b13e38
                | exact resolve b13e38 b13e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e249 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b13e45 (σ X0) (σ X0)
                   have i₂ := b13e87 X0
                   grind)
                | exact superpose b13e87 b13e45
                | exact resolve b13e45 b13e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e45
              have b13e254 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e18 X1 (σ X0)
                   have i₂ := b13e87 X0
                   grind)
                | exact superpose b13e87 b13e18
                | (have j0 := b13e18 X1 (σ X0)
                   grind)
                | exact resolve b13e18 b13e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e261 : (M.op x y) = (M.op x x) ∨ y = (k y x) := by
                first
                | (have j0 := b13e97 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e97
              have b13e262 : y = (k y x) := by
                first
                | (have r₁ := b13e261
                   have r₂ := b13e27
                   grind)
                | exact resolve b13e261 b13e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e261
              have b13e749 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e248 (M.op X0 X1) X1
                   have i₂ := b13e38 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b13e38 b13e248
                | exact resolve b13e248 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e248
              have b13e951 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e182 x y
                   grind)
                | exact superpose b13e182 b13e22
                | (have j1 := b13e182 x y
                   grind)
                | exact resolve b13e22 b13e182
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e974 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e38 (σ X0) (σ X1) x
                   have i₂ := b13e182 X0 X1
                   grind)
                | exact superpose b13e182 b13e38
                | (have j1 := b13e182 X1 X0
                   grind)
                | exact resolve b13e38 b13e182
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e38 b13e182
              have b13e1024 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e951
                   have i₂ := b13e262
                   grind)
                | exact superpose b13e262 b13e951
                | exact resolve b13e951 b13e262
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e951
              have b13e1098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e1024
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e1024
                | exact resolve b13e1024 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1024
              have b13e1145 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b13e1098
                   have r₂ := b13e22
                   grind)
                | exact resolve b13e1098 b13e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1098
              have b13e3215 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
                first
                | (have i₁ := b13e249 y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e249
                | exact resolve b13e249 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e249
              have b13e25621 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b13e974 y x x
                   have i₂ := b13e262
                   grind)
                | exact superpose b13e262 b13e974
                | (have j0 := b13e974 y x x
                   grind)
                | exact resolve b13e974 b13e262
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e974
              have b13e26785 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b13e25621 X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e25621
                | (have j0 := b13e25621 X0
                   grind)
                | exact resolve b13e25621 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e25621
              have b13e26950 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have j0 := b13e26785 X0
                   grind)
                | (have r₁ := b13e26785 X0
                   have r₂ := b13e22
                   grind)
                | exact resolve b13e26785 b13e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e26785
              have b13e27238 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e3215
                   have i₂ := b13e26950 (σ (M.op x y))
                   grind)
                | exact superpose b13e26950 b13e3215
                | exact resolve b13e3215 b13e26950
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e3215 b13e26950
              have b13e27346 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b13e27238
                   have r₂ := b13e1145
                   grind)
                | exact resolve b13e27238 b13e1145
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1145 b13e27238
              have b13e28837 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e254 x (σ y)
                   have i₂ := b13e27346
                   grind)
                | exact superpose b13e27346 b13e254
                | (have j0 := b13e254 x (σ y)
                   grind)
                | (have r₁ := b13e254 x (σ y)
                   have r₂ := b13e27346
                   grind)
                | exact resolve b13e254 b13e27346
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e254 b13e27346
              have b13e28892 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
              clear b13e28837
              have b13e28908 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
                first
                | (have i₁ := b13e28892
                   have i₂ := b13e21 y x
                   grind)
                | exact superpose b13e21 b13e28892
                | exact resolve b13e28892 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e28892
              have b13e28924 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b13e28908
                   have i₂ := b13e262
                   grind)
                | exact superpose b13e262 b13e28908
                | exact resolve b13e28908 b13e262
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e262 b13e28908
              have b13e28939 : (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e28924
                   have i₂ := b13e87 y
                   grind)
                | exact superpose b13e87 b13e28924
                | exact resolve b13e28924 b13e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e87 b13e28924
              have b13e28949 : (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b13e28939
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e28939
                | exact resolve b13e28939 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e28939
              have b13e30379 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b13e749 x y x
                   have i₂ := b13e28949
                   grind)
                | exact superpose b13e28949 b13e749
                | exact resolve b13e749 b13e28949
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e749
              have b13e34818 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e30379 (σ x)
                   grind)
                | exact superpose b13e30379 b13e22
                | exact resolve b13e22 b13e30379
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30379
              have b13e34857 : False := by grind
              exact b13e34857
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b14e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              have b14e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b14e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e25
                | exact resolve b14e25 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b14e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e39 X0 X1 x X3
                   have i₂ := b14e15 X0 X1 x
                   grind)
                | exact superpose b14e15 b14e39
                | exact resolve b14e39 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39
              have b14e77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b14e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e84 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b14e21 X0 X0
                   have i₂ := b14e77 (σ X0)
                   grind)
                | exact superpose b14e77 b14e21
                | exact resolve b14e21 b14e77
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b14e84 X0
                   have i₂ := b14e77 X0
                   grind)
                | exact superpose b14e77 b14e84
                | exact resolve b14e84 b14e77
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e77 b14e84
              have b14e147 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e19 X0 X1
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e19 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e19
                | (have j0 := b14e19 X0 X1
                   have j1 := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e19 X1 X1
                   have r₂ := b14e20 X1 X1
                   grind)
                | (have r₁ := b14e19 X0 X0
                   have r₂ := b14e20 X0 X0
                   grind)
                | (have r₁ := b14e19 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | exact resolve b14e19 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 X0
                   have i₂ := b14e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e166 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b14e20 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e168 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e147 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e147
              have b14e171 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e162 X0 X1
                   have i₂ := b14e89 X0
                   grind)
                | exact superpose b14e89 b14e162
                | (have j0 := b14e162 X0 X1
                   grind)
                | exact resolve b14e162 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e162
              have b14e174 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b14e168 X0 X1
                   have j1 := b14e166 X1 X0
                   grind)
                | (have r₁ := b14e168 X0 X1
                   have r₂ := b14e166 X0 X1
                   grind)
                | (have r₁ := b14e168 X1 X0
                   have r₂ := b14e166 X0 X1
                   grind)
                | (have r₁ := b14e168 X0 X0
                   have r₂ := b14e166 X0 X0
                   grind)
                | exact resolve b14e168 b14e166
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e166 b14e168
              have b14e184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e171 X0 X1
                   have i₂ := b14e89 X1
                   grind)
                | exact superpose b14e89 b14e171
                | (have j0 := b14e171 X0 X1
                   grind)
                | exact resolve b14e171 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e171
              have b14e204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e174 (σ X0) (σ X1)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e174
                | (have j0 := b14e174 (σ X0) (σ X1)
                   grind)
                | exact resolve b14e174 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e174
              have b14e249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e204 X0 X1
                   have i₂ := b14e89 X1
                   grind)
                | exact superpose b14e89 b14e204
                | (have j0 := b14e204 X0 X1
                   grind)
                | exact resolve b14e204 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e204
              have b14e325 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b14e29
                   have i₂ := b14e89 y
                   grind)
                | exact superpose b14e89 b14e29
                | exact resolve b14e29 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29
              have b14e331 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e18 X1 (σ X0)
                   have i₂ := b14e89 X0
                   grind)
                | exact superpose b14e89 b14e18
                | (have j0 := b14e18 X1 (σ X0)
                   grind)
                | exact resolve b14e18 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e343 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b14e325
                   have i₂ := b14e89 x
                   grind)
                | exact superpose b14e89 b14e325
                | exact resolve b14e325 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e325
              have b14e778 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e184 x y
                   grind)
                | exact superpose b14e184 b14e22
                | (have j1 := b14e184 x y
                   grind)
                | exact resolve b14e22 b14e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e184
              have b14e9122 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e19 (σ X0) (σ X1)
                   have i₂ := b14e249 X0 X1
                   grind)
                | exact superpose b14e249 b14e19
                | (have j0 := b14e19 (σ X0) (σ X1)
                   have j1 := b14e249 X0 X1
                   grind)
                | exact resolve b14e19 b14e249
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e9272 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
                intro X0 X1
                first
                | (have j0 := b14e249 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e9341 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e9122 X0 X1
                   have i₂ := b14e89 X0
                   grind)
                | exact superpose b14e89 b14e9122
                | (have j0 := b14e9122 X0 X1
                   grind)
                | exact resolve b14e9122 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e9122
              have b14e9455 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e9341 X0 X1
                   have i₂ := b14e89 X1
                   grind)
                | exact superpose b14e89 b14e9341
                | (have j0 := b14e9341 X0 X1
                   grind)
                | exact resolve b14e9341 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e9341
              have b14e9526 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have j0 := b14e9455 X0 X1
                   have j1 := b14e9272 X1 X0
                   grind)
                | (have r₁ := b14e9455 X1 X0
                   have r₂ := b14e9272 X0 X1
                   grind)
                | (have r₁ := b14e9455 (M.op X0 X0) X0
                   have r₂ := b14e9272 X0 (M.op X0 X0)
                   grind)
                | exact resolve b14e9455 b14e9272
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e9272 b14e9455
              have b14e9567 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e9526 X0 X1
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e9526
                | (have j0 := b14e9526 X0 X1
                   grind)
                | exact resolve b14e9526 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e9526
              have b14e9568 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have j0 := b14e9567 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e9567
              have b14e17185 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b14e778
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e778
                | (have j1 := b14e20 y x
                   grind)
                | exact resolve b14e778 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e778
              have b14e17202 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
              clear b14e17185
              have b14e17211 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b14e17202
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e17202 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e17202
              have b14e17212 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b14e17211
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e17211 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e17211
              have b14e56280 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b14e249 y x
                   have i₂ := b14e17212
                   grind)
                | exact superpose b14e17212 b14e249
                | (have j0 := b14e249 y x
                   grind)
                | exact resolve b14e249 b14e17212
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e249 b14e17212
              have b14e56405 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have j1 := b14e9568 y x
                   grind)
                | (have r₁ := b14e56280
                   have r₂ := b14e9568 y x
                   grind)
                | exact resolve b14e56280 b14e9568
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e9568 b14e56280
              have b14e56442 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have r₁ := b14e56405
                   have r₂ := b14e343
                   grind)
                | exact resolve b14e56405 b14e343
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e343 b14e56405
              have b14e56659 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e331 x (σ y)
                   have i₂ := b14e56442
                   grind)
                | exact superpose b14e56442 b14e331
                | (have j0 := b14e331 x (σ y)
                   grind)
                | (have r₁ := b14e331 x (σ y)
                   have r₂ := b14e56442
                   grind)
                | exact resolve b14e331 b14e56442
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e331 b14e56442
              have b14e56744 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by grind
              clear b14e56659
              have b14e56767 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e56744
                   have i₂ := b14e21 y x
                   grind)
                | exact superpose b14e21 b14e56744
                | exact resolve b14e56744 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e56744
              have b14e56788 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e56767
                   have i₂ := b14e89 y
                   grind)
                | exact superpose b14e89 b14e56767
                | exact resolve b14e56767 b14e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e89 b14e56767
              have b14e57436 : (k y x) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e16 (k y x)
                   have i₂ := b14e56788
                   grind)
                | exact superpose b14e56788 b14e16
                | exact resolve b14e16 b14e56788
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e56788
              have b14e57535 : (σ y) = (σ (k y x)) ∨ (M.op y y) = (k y x) := by
                first
                | (have i₁ := b14e57436
                   have i₂ := b14e16 (M.op y y)
                   grind)
                | exact superpose b14e16 b14e57436
                | exact resolve b14e57436 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e57436
              have b14e59723 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b14e57535
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e57535
                | (have j1 := b14e20 y x
                   grind)
                | exact resolve b14e57535 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e57535
              have b14e59829 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
              clear b14e59723
              have b14e59870 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
                first
                | (have r₁ := b14e59829
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e59829 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59829
              have b14e59878 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b14e59870
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e59870 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59870
              have b14e61867 : (M.op x y) = (τ (σ y)) := by
                first
                | (have i₁ := b14e16 (M.op x y)
                   have i₂ := b14e59878
                   grind)
                | exact superpose b14e59878 b14e16
                | exact resolve b14e16 b14e59878
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59878
              have b14e61992 : y = (M.op x y) := by
                first
                | (have i₁ := b14e61867
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e61867
                | exact resolve b14e61867 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e61867
              have b14e62223 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e40 x y x
                   have i₂ := b14e61992
                   grind)
                | exact superpose b14e61992 b14e40
                | exact resolve b14e40 b14e61992
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40
              have b14e66914 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e62223 y
                   grind)
                | exact superpose b14e62223 b14e28
                | exact resolve b14e28 b14e62223
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e62223
              have b14e66928 : False := by grind
              exact b14e66928
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b15e23 : (M.op y x) = (M.op x x) := by grind
            have b15e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b15e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : (M.op y y) ≠ (M.op x x) := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e22
              | exact resolve b15e22 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b15e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e34 X0 X1 x X3
                 have i₂ := b15e14 X0 X1 x
                 grind)
              | exact superpose b15e14 b15e34
              | exact resolve b15e34 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e82 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ x = (k x y) := by
              first
              | (have i₁ := b15e18 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x x
                 grind)
              | (have r₁ := b15e18 x y
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e86 : (M.op y y) = (M.op x x) ∨ x = (k x y) := by grind
            clear b15e82
            have b15e89 : x = (k x y) := by
              first
              | (have r₁ := b15e86
                 have r₂ := b15e27
                 grind)
              | exact resolve b15e86 b15e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27 b15e86
            have b15e126 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b15e24
                 have i₂ := b15e19 X0 (σ y)
                 grind)
              | (have i₁ := b15e24
                 have i₂ := b15e19 (σ y) (σ y)
                 grind)
              | exact superpose b15e19 b15e24
              | (have j1 := b15e19 X0 (σ y)
                 grind)
              | (have r₁ := b15e24
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | exact resolve b15e24 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e547 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b15e126 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e126
            have b15e548 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e547
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e547 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e547
            have b15e549 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e548
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e548
              | exact resolve b15e548 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e548
            have b15e550 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e549
                 have i₂ := b15e89
                 grind)
              | exact superpose b15e89 b15e549
              | exact resolve b15e549 b15e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e89 b15e549
            have b15e553 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e550
                 grind)
              | exact superpose b15e550 b15e25
              | exact resolve b15e25 b15e550
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e557 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e35 (σ y) (σ x) x
                 have i₂ := b15e550
                 grind)
              | exact superpose b15e550 b15e35
              | exact resolve b15e35 b15e550
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35 b15e550
            have b15e563 : False := by grind
            exact b15e563
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e24 : (M.op y x) = (M.op x x) := by grind
              have b16e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b16e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
              have b16e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b16e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b16e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b16e36 X0 X1 x X3
                   have i₂ := b16e15 X0 X1 x
                   grind)
                | exact superpose b16e15 b16e36
                | exact resolve b16e36 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36
              have b16e86 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ x = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x x
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e94 : (M.op y y) = (M.op x x) ∨ x = (k x y) := by grind
              clear b16e86
              have b16e99 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
                first
                | (have i₁ := b16e94
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e94
                | exact resolve b16e94 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e94
              have b16e104 : x = (k x y) := by
                first
                | (have r₁ := b16e99
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e99 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e99
              have b16e135 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b16e25
                   have i₂ := b16e20 X0 (σ y)
                   grind)
                | (have i₁ := b16e25
                   have i₂ := b16e20 (σ y) (σ y)
                   grind)
                | exact superpose b16e20 b16e25
                | (have j1 := b16e20 X0 (σ y)
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e25 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e510 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b16e135 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e135
              have b16e511 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b16e510
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e510 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e510
              have b16e512 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e511
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e511
                | exact resolve b16e511 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e511
              have b16e513 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e512
                   have i₂ := b16e104
                   grind)
                | exact superpose b16e104 b16e512
                | exact resolve b16e512 b16e104
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e104 b16e512
              have b16e516 : (σ x) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b16e26
                   have i₂ := b16e513
                   grind)
                | exact superpose b16e513 b16e26
                | exact resolve b16e26 b16e513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e520 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e37 (σ y) (σ x) x
                   have i₂ := b16e513
                   grind)
                | exact superpose b16e513 b16e37
                | exact resolve b16e37 b16e513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e37 b16e513
              have b16e526 : False := by grind
              exact b16e526
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : (M.op y x) ≠ (M.op y y) := by grind
              have b17e24 : (M.op y x) = (M.op x x) := by grind
              have b17e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b17e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : (M.op y y) ≠ (M.op x x) := by
                first
                | (have i₁ := b17e23
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e23
                | exact resolve b17e23 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b17e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b17e38 X0 X1 x X3
                   have i₂ := b17e15 X0 X1 x
                   grind)
                | exact superpose b17e15 b17e38
                | exact resolve b17e38 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e38
              have b17e89 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ x = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x x
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e96 : (M.op y y) = (M.op x x) ∨ x = (k x y) := by grind
              clear b17e89
              have b17e101 : x = (k x y) := by
                first
                | (have r₁ := b17e96
                   have r₂ := b17e29
                   grind)
                | exact resolve b17e96 b17e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e29 b17e96
              have b17e136 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (σ y)
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ y) (σ y)
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 X0 (σ y)
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e430 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b17e136 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e136
              have b17e431 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e430
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e430 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e430
              have b17e432 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e431
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e431
                | exact resolve b17e431 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e431
              have b17e433 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e432
                   have i₂ := b17e101
                   grind)
                | exact superpose b17e101 b17e432
                | exact resolve b17e432 b17e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e101 b17e432
              have b17e435 : (σ x) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e433
                   grind)
                | exact superpose b17e433 b17e26
                | exact resolve b17e26 b17e433
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e439 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e39 (σ y) (σ x) x
                   have i₂ := b17e433
                   grind)
                | exact superpose b17e433 b17e39
                | exact resolve b17e39 b17e433
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e39 b17e433
              have b17e445 : False := by grind
              exact b17e445
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b18e22 : (M.op y x) ≠ (M.op x x) := by grind
          have b18e23 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e63 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e16 X0 (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 X0 (σ y)
               grind)
            | (have r₁ := b18e16 (σ x) (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b18e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b18e19 X0 X0
               have i₂ := b18e64 (σ X0)
               grind)
            | exact superpose b18e64 b18e19
            | exact resolve b18e19 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b18e75 X0
               have i₂ := b18e64 X0
               grind)
            | exact superpose b18e64 b18e75
            | exact resolve b18e75 b18e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e64 b18e75
          have b18e306 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b18e63 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e63
          have b18e309 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e306
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e306
            | exact resolve b18e306 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e306
          have b18e319 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e309
               have i₂ := b18e76 x
               grind)
            | exact superpose b18e76 b18e309
            | exact resolve b18e309 b18e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e76 b18e309
          have b18e338 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e319
               grind)
            | exact superpose b18e319 b18e14
            | exact resolve b18e14 b18e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e319
          have b18e339 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b18e338
               have i₂ := b18e14 (M.op x x)
               grind)
            | exact superpose b18e14 b18e338
            | exact resolve b18e338 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e338
          have b18e428 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b18e18 x y
               have i₂ := b18e339
               grind)
            | exact superpose b18e339 b18e18
            | (have j0 := b18e18 x y
               grind)
            | exact resolve b18e18 b18e339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e339
          have b18e429 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
          clear b18e428
          have b18e431 : (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b18e429
               have r₂ := b18e22
               grind)
            | exact resolve b18e429 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429
          have b18e435 : False := by grind
          exact b18e435
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b19e23 : (M.op y x) ≠ (M.op x x) := by grind
            have b19e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e66 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e17
              | (have j0 := b19e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b19e17 (σ x) (σ y)
                 have r₂ := b19e24
                 grind)
              | exact resolve b19e17 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b19e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e70 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b19e66
            have b19e72 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e70
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e70
              | exact resolve b19e70 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e70
            have b19e205 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ x)
                 have i₂ := b19e72
                 grind)
              | exact superpose b19e72 b19e17
              | exact resolve b19e17 b19e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e72
            have b19e209 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
            clear b19e205
            have b19e210 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b19e209
                 have i₂ := b19e20 x x
                 grind)
              | exact superpose b19e20 b19e209
              | exact resolve b19e209 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e209
            have b19e212 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b19e210
                 have i₂ := b19e69 x
                 grind)
              | exact superpose b19e69 b19e210
              | exact resolve b19e210 b19e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e69 b19e210
            have b19e224 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e212
                 grind)
              | exact superpose b19e212 b19e15
              | exact resolve b19e15 b19e212
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e212
            have b19e225 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b19e224
                 have i₂ := b19e15 (M.op x x)
                 grind)
              | exact superpose b19e15 b19e224
              | exact resolve b19e224 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e224
            have b19e292 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b19e19 x y
                 have i₂ := b19e225
                 grind)
              | exact superpose b19e225 b19e19
              | (have j0 := b19e19 x y
                 grind)
              | exact resolve b19e19 b19e225
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e225
            have b19e293 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
            clear b19e292
            have b19e295 : (M.op y x) = (M.op y y) := by
              first
              | (have r₁ := b19e293
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e293 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e293
            have b19e299 : False := by grind
            exact b19e299
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b20e23 : (M.op y x) ≠ (M.op x x) := by grind
            have b20e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e61 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b20e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e65 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b20e61
            have b20e67 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b20e65
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e65
              | exact resolve b20e65 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e65
            have b20e194 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ x)
                 have i₂ := b20e67
                 grind)
              | exact superpose b20e67 b20e17
              | exact resolve b20e17 b20e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e67
            have b20e198 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
            clear b20e194
            have b20e199 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b20e198
                 have i₂ := b20e20 x x
                 grind)
              | exact superpose b20e20 b20e198
              | exact resolve b20e198 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e198
            have b20e201 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b20e199
                 have i₂ := b20e64 x
                 grind)
              | exact superpose b20e64 b20e199
              | exact resolve b20e199 b20e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e64 b20e199
            have b20e205 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e201
                 grind)
              | exact superpose b20e201 b20e15
              | exact resolve b20e15 b20e201
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e201
            have b20e206 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b20e205
                 have i₂ := b20e15 (M.op x x)
                 grind)
              | exact superpose b20e15 b20e205
              | exact resolve b20e205 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e205
            have b20e222 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b20e19 x y
                 have i₂ := b20e206
                 grind)
              | exact superpose b20e206 b20e19
              | (have j0 := b20e19 x y
                 grind)
              | exact resolve b20e19 b20e206
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e206
            have b20e223 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
            clear b20e222
            have b20e225 : (M.op y x) = (M.op y y) := by
              first
              | (have r₁ := b20e223
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e223 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e223
            have b20e227 : False := by grind
            exact b20e227
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b21e23 : (M.op y x) ≠ (M.op x x) := by grind
            have b21e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b21e25 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e24
              | exact resolve b21e24 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b21e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b21e33 X0 X1 x X3
                 have i₂ := b21e14 X0 X1 x
                 grind)
              | exact superpose b21e14 b21e33
              | exact resolve b21e33 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e33
            have b21e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 X1 x
                 have i₂ := b21e34 (M.op X0 X1) X1 x
                 grind)
              | exact superpose b21e34 b21e14
              | exact resolve b21e14 b21e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e34
            have b21e82 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ x)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e86 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b21e82
            have b21e89 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e86
                 have r₂ := b21e27
                 grind)
              | exact resolve b21e86 b21e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e27 b21e86
            have b21e94 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e89
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e89
              | exact resolve b21e89 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e89
            have b21e176 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e94
                 grind)
              | exact superpose b21e94 b21e15
              | exact resolve b21e15 b21e94
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e94
            have b21e177 : x = (k x y) := by
              first
              | (have i₁ := b21e176
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e176
              | exact resolve b21e176 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e176
            have b21e191 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e177
                 grind)
              | exact superpose b21e177 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e177
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e177
            have b21e192 : x = (M.op y x) ∨ (M.op y x) = (M.op x x) := by
              first
              | (have r₁ := b21e191
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e191 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e191
            have b21e194 : x = (M.op y x) := by
              first
              | (have r₁ := b21e192
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e192 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e192
            have b21e208 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e194
                 grind)
              | exact superpose b21e194 b21e23
              | exact resolve b21e23 b21e194
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e212 : x = (M.op x x) := by
              first
              | (have i₁ := b21e40 y x
                 have i₂ := b21e194
                 grind)
              | exact superpose b21e194 b21e40
              | exact resolve b21e40 b21e194
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e40 b21e194
            have b21e214 : False := by grind
            exact b21e214
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : (M.op y x) ≠ (M.op y y) := by grind
              have b22e24 : (M.op y x) ≠ (M.op x x) := by grind
              have b22e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b22e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              have b22e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b22e25
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e25
                | exact resolve b22e25 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e30 : (M.op x y) ≠ (M.op y x) := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e23
                | exact resolve b22e23 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b22e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b22e39 X0 X1 x X3
                   have i₂ := b22e15 X0 X1 x
                   grind)
                | exact superpose b22e15 b22e39
                | exact resolve b22e39 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39
              have b22e46 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 X1 x
                   have i₂ := b22e40 (M.op X0 X1) X1 x
                   grind)
                | exact superpose b22e40 b22e15
                | exact resolve b22e15 b22e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e40
              have b22e100 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ x)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e105 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b22e100
              have b22e108 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e105
                   have r₂ := b22e29
                   grind)
                | exact resolve b22e105 b22e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e29 b22e105
              have b22e113 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e108
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e108
                | exact resolve b22e108 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e108
              have b22e120 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e113
                   grind)
                | exact superpose b22e113 b22e16
                | exact resolve b22e16 b22e113
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e113
              have b22e121 : x = (k x y) := by
                first
                | (have i₁ := b22e120
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e120
                | exact resolve b22e120 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e120
              have b22e201 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e121
                   grind)
                | exact superpose b22e121 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e121
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e121
              have b22e202 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
                first
                | (have r₁ := b22e201
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e201 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e201
              have b22e204 : (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b22e202
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e202
                | exact resolve b22e202 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e202
              have b22e206 : x = (M.op y x) := by
                first
                | (have r₁ := b22e204
                   have r₂ := b22e30
                   grind)
                | exact resolve b22e204 b22e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e30 b22e204
              have b22e218 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b22e24
                   have i₂ := b22e206
                   grind)
                | exact superpose b22e206 b22e24
                | exact resolve b22e24 b22e206
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e223 : x = (M.op x x) := by
                first
                | (have i₁ := b22e46 y x
                   have i₂ := b22e206
                   grind)
                | exact superpose b22e206 b22e46
                | exact resolve b22e46 b22e206
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e46 b22e206
              have b22e226 : False := by grind
              exact b22e226
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : (M.op y x) ≠ (M.op y y) := by grind
              have b23e24 : (M.op y x) ≠ (M.op x x) := by grind
              have b23e25 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b23e26 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b23e25
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e25
                | exact resolve b23e25 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b23e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b23e37 X0 X1 x X3
                   have i₂ := b23e15 X0 X1 x
                   grind)
                | exact superpose b23e15 b23e37
                | exact resolve b23e37 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 X1 x
                   have i₂ := b23e38 (M.op X0 X1) X1 x
                   grind)
                | exact superpose b23e38 b23e15
                | exact resolve b23e15 b23e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e91 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ x)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e96 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b23e91
              have b23e99 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e96
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e96 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29 b23e96
              have b23e104 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e99
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e99
                | exact resolve b23e99 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e99
              have b23e111 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e104
                   grind)
                | exact superpose b23e104 b23e16
                | exact resolve b23e16 b23e104
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e104
              have b23e112 : x = (k x y) := by
                first
                | (have i₁ := b23e111
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e111
                | exact resolve b23e111 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e111
              have b23e191 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e112
                   grind)
                | exact superpose b23e112 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e112
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e112
              have b23e192 : x = (M.op y x) ∨ (M.op y x) = (M.op x x) := by
                first
                | (have r₁ := b23e191
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e191 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e191
              have b23e194 : x = (M.op y x) := by
                first
                | (have r₁ := b23e192
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e192 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e192
              have b23e244 : x ≠ (M.op x x) := by
                first
                | (have i₁ := b23e24
                   have i₂ := b23e194
                   grind)
                | exact superpose b23e194 b23e24
                | exact resolve b23e24 b23e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e248 : x = (M.op x x) := by
                first
                | (have i₁ := b23e43 y x
                   have i₂ := b23e194
                   grind)
                | exact superpose b23e194 b23e43
                | exact resolve b23e43 b23e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e43 b23e194
              have b23e250 : False := by grind
              exact b23e250
        · rcases eq_or_ne (M.op x y) (M.op x x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : (M.op y x) ≠ (M.op y y) := by grind
            have b24e26 : (M.op x y) = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b24e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b24e32 X0 X1 x X3
                 have i₂ := b24e14 X0 X1 x
                 grind)
              | exact superpose b24e14 b24e32
              | exact resolve b24e32 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32
            have b24e39 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 X1 x
                 have i₂ := b24e33 (M.op X0 X1) X1 x
                 grind)
              | exact superpose b24e33 b24e14
              | exact resolve b24e14 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e58 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by
              first
              | (have i₁ := b24e17 y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e17
              | (have j0 := b24e17 x x
                 grind)
              | (have r₁ := b24e17 y x
                 have r₂ := b24e26
                 grind)
              | exact resolve b24e17 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b24e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e64 : (M.op y y) = (k y x) := by grind
            clear b24e58
            have b24e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b24e20 X0 X0
                 have i₂ := b24e63 (σ X0)
                 grind)
              | exact superpose b24e63 b24e20
              | exact resolve b24e20 b24e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b24e71 X0
                 have i₂ := b24e63 X0
                 grind)
              | exact superpose b24e63 b24e71
              | exact resolve b24e71 b24e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e63 b24e71
            have b24e122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e18 X0 X1
                 have i₂ := b24e19 X0 X1
                 grind)
              | (have i₁ := b24e18 X0 X0
                 have i₂ := b24e19 X0 X1
                 grind)
              | exact superpose b24e19 b24e18
              | (have j0 := b24e18 X0 X1
                 have j1 := b24e19 X0 X1
                 grind)
              | (have r₁ := b24e18 X1 X1
                 have r₂ := b24e19 X1 X1
                 grind)
              | (have r₁ := b24e18 X0 X0
                 have r₂ := b24e19 X0 X0
                 grind)
              | (have r₁ := b24e18 X0 X1
                 have r₂ := b24e19 X0 X1
                 grind)
              | exact resolve b24e18 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e136 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e139 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
              intro X0 X1
              first
              | (have j0 := b24e19 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e142 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b24e122 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e122
            have b24e146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e136 X0 X1
                 have i₂ := b24e72 X0
                 grind)
              | exact superpose b24e72 b24e136
              | (have j0 := b24e136 X0 X1
                 grind)
              | exact resolve b24e136 b24e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e136
            have b24e148 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
              intro X0 X1
              first
              | (have j0 := b24e142 X0 X1
                 have j1 := b24e139 X1 X0
                 grind)
              | (have r₁ := b24e142 X0 X1
                 have r₂ := b24e139 X0 X1
                 grind)
              | (have r₁ := b24e142 X1 X0
                 have r₂ := b24e139 X0 X1
                 grind)
              | (have r₁ := b24e142 X0 X0
                 have r₂ := b24e139 X0 X0
                 grind)
              | exact resolve b24e142 b24e139
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e139 b24e142
            have b24e157 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e146 X0 X1
                 have i₂ := b24e72 X1
                 grind)
              | exact superpose b24e72 b24e146
              | (have j0 := b24e146 X0 X1
                 grind)
              | exact resolve b24e146 b24e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e146
            have b24e250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e148 (σ X0) (σ X1)
                 have i₂ := b24e20 X0 X1
                 grind)
              | exact superpose b24e20 b24e148
              | (have j0 := b24e148 (σ X0) (σ X1)
                 grind)
              | exact resolve b24e148 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e148
            have b24e302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e250 X0 X1
                 have i₂ := b24e72 X1
                 grind)
              | exact superpose b24e72 b24e250
              | (have j0 := b24e250 X0 X1
                 grind)
              | exact resolve b24e250 b24e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e250
            have b24e775 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e157 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e157
            have b24e8278 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e18 (σ X0) (σ X1)
                 have i₂ := b24e302 X0 X1
                 grind)
              | exact superpose b24e302 b24e18
              | (have j0 := b24e18 (σ X0) (σ X1)
                 have j1 := b24e302 X0 X1
                 grind)
              | exact resolve b24e18 b24e302
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e8405 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e302 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e8461 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e8278 X0 X1
                 have i₂ := b24e72 X0
                 grind)
              | exact superpose b24e72 b24e8278
              | (have j0 := b24e8278 X0 X1
                 grind)
              | exact resolve b24e8278 b24e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e8278
            have b24e8575 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e8461 X0 X1
                 have i₂ := b24e72 X1
                 grind)
              | exact superpose b24e72 b24e8461
              | (have j0 := b24e8461 X0 X1
                 grind)
              | exact resolve b24e8461 b24e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e72 b24e8461
            have b24e8647 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have j0 := b24e8575 X0 X1
                 have j1 := b24e8405 X1 X0
                 grind)
              | (have r₁ := b24e8575 X1 X0
                 have r₂ := b24e8405 X0 X1
                 grind)
              | (have r₁ := b24e8575 (M.op X0 X0) X0
                 have r₂ := b24e8405 X0 (M.op X0 X0)
                 grind)
              | exact resolve b24e8575 b24e8405
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e8405 b24e8575
            have b24e8689 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e8647 X0 X1
                 have i₂ := b24e20 X0 X1
                 grind)
              | exact superpose b24e20 b24e8647
              | (have j0 := b24e8647 X0 X1
                 grind)
              | exact resolve b24e8647 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e8647
            have b24e8690 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
              intro X0 X1
              first
              | (have j0 := b24e8689 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e8689
            have b24e16395 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b24e775 x y
                 have i₂ := b24e64
                 grind)
              | exact superpose b24e64 b24e775
              | (have j0 := b24e775 x y
                 grind)
              | exact resolve b24e775 b24e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e775
            have b24e16458 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
            clear b24e16395
            have b24e16501 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
              first
              | (have r₁ := b24e16458
                 have r₂ := b24e27
                 grind)
              | exact resolve b24e16458 b24e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e16458
            have b24e16649 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b24e16501
                 have i₂ := b24e302 y x
                 grind)
              | exact superpose b24e302 b24e16501
              | (have j1 := b24e302 y x
                 grind)
              | exact resolve b24e16501 b24e302
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e302 b24e16501
            have b24e16722 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have j1 := b24e8690 y x
                 grind)
              | (have r₁ := b24e16649
                 have r₂ := b24e8690 y x
                 grind)
              | exact resolve b24e16649 b24e8690
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e8690 b24e16649
            have b24e16731 : (σ y) = (σ (k y x)) := by
              first
              | (have r₁ := b24e16722
                 have r₂ := b24e27
                 grind)
              | exact resolve b24e16722 b24e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e27 b24e16722
            have b24e16735 : (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b24e16731
                 have i₂ := b24e64
                 grind)
              | exact superpose b24e64 b24e16731
              | exact resolve b24e16731 b24e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e64 b24e16731
            have b24e16952 : (M.op y y) = (τ (σ y)) := by
              first
              | (have i₁ := b24e15 (M.op y y)
                 have i₂ := b24e16735
                 grind)
              | exact superpose b24e16735 b24e15
              | exact resolve b24e15 b24e16735
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e16735
            have b24e17016 : y = (M.op y y) := by
              first
              | (have i₁ := b24e16952
                 have i₂ := b24e15 y
                 grind)
              | exact superpose b24e15 b24e16952
              | exact resolve b24e16952 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e16952
            have b24e17271 : y ≠ (M.op y x) := by
              first
              | (have i₁ := b24e22
                 have i₂ := b24e17016
                 grind)
              | exact superpose b24e17016 b24e22
              | exact resolve b24e22 b24e17016
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e17296 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b24e33 y y x
                 have i₂ := b24e17016
                 grind)
              | exact superpose b24e17016 b24e33
              | exact resolve b24e33 b24e17016
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33 b24e17016
            have b24e17904 : y = (M.op x x) := by
              first
              | (have i₁ := b24e26
                 have i₂ := b24e17296 x
                 grind)
              | exact superpose b24e17296 b24e26
              | exact resolve b24e26 b24e17296
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e17296
            have b24e20333 : y = (M.op y x) := by
              first
              | (have i₁ := b24e39 x x
                 have i₂ := b24e17904
                 grind)
              | exact superpose b24e17904 b24e39
              | exact resolve b24e39 b24e17904
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e39 b24e17904
            have b24e20362 : False := by grind
            exact b24e20362
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b25e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b25e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e38 X0 X1 x X3
                   have i₂ := b25e15 X0 X1 x
                   grind)
                | exact superpose b25e15 b25e38
                | exact resolve b25e38 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 X1 x
                   have i₂ := b25e39 (M.op X0 X1) X1 x
                   grind)
                | exact superpose b25e39 b25e15
                | exact resolve b25e15 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b25e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e84 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b25e21 X0 X0
                   have i₂ := b25e75 (σ X0)
                   grind)
                | exact superpose b25e75 b25e21
                | exact resolve b25e21 b25e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e84 X0
                   have i₂ := b25e75 X0
                   grind)
                | exact superpose b25e75 b25e84
                | exact resolve b25e84 b25e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e75 b25e84
              have b25e96 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ y = (k y X0) := by
                intro X0
                first
                | (have i₁ := b25e19 y X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e19
                | (have j0 := b25e19 y X0
                   grind)
                | (have r₁ := b25e19 y x
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e19 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e168 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e176 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e168 X0 X1
                   have i₂ := b25e89 X0
                   grind)
                | exact superpose b25e89 b25e168
                | (have j0 := b25e168 X0 X1
                   grind)
                | exact resolve b25e168 b25e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e168
              have b25e187 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e176 X0 X1
                   have i₂ := b25e89 X1
                   grind)
                | exact superpose b25e89 b25e176
                | (have j0 := b25e176 X0 X1
                   grind)
                | exact resolve b25e176 b25e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e176
              have b25e236 : (M.op x y) = (M.op x x) ∨ y = (k y x) := by
                first
                | (have j0 := b25e96 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e96
              have b25e237 : y = (k y x) := by
                first
                | (have r₁ := b25e236
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e236 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e236
              have b25e304 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e18 X1 (σ X0)
                   have i₂ := b25e89 X0
                   grind)
                | exact superpose b25e89 b25e18
                | (have j0 := b25e18 X1 (σ X0)
                   grind)
                | exact resolve b25e18 b25e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e307 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b25e39 (σ X0) (σ X0) x
                   have i₂ := b25e89 X0
                   grind)
                | exact superpose b25e89 b25e39
                | exact resolve b25e39 b25e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e308 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b25e45 (σ X0) (σ X0)
                   have i₂ := b25e89 X0
                   grind)
                | exact superpose b25e89 b25e45
                | exact resolve b25e45 b25e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e45
              have b25e733 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e187 x y
                   grind)
                | exact superpose b25e187 b25e22
                | (have j1 := b25e187 x y
                   grind)
                | exact resolve b25e22 b25e187
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e752 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e39 (σ X0) (σ X1) x
                   have i₂ := b25e187 X0 X1
                   grind)
                | exact superpose b25e187 b25e39
                | (have j1 := b25e187 X1 X0
                   grind)
                | exact resolve b25e39 b25e187
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e187
              have b25e797 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e733
                   have i₂ := b25e237
                   grind)
                | exact superpose b25e237 b25e733
                | exact resolve b25e733 b25e237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e733
              have b25e868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e797
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e797
                | exact resolve b25e797 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e797
              have b25e913 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b25e868
                   have r₂ := b25e22
                   grind)
                | exact resolve b25e868 b25e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e868
              have b25e2525 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e307 (M.op X0 X1) X1
                   have i₂ := b25e39 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b25e39 b25e307
                | exact resolve b25e307 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39 b25e307
              have b25e6361 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
                first
                | (have i₁ := b25e308 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e308
                | exact resolve b25e308 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e308
              have b25e22480 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b25e752 y x x
                   have i₂ := b25e237
                   grind)
                | exact superpose b25e237 b25e752
                | (have j0 := b25e752 y x x
                   grind)
                | exact resolve b25e752 b25e237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e752
              have b25e23561 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b25e22480 X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e22480
                | (have j0 := b25e22480 X0
                   grind)
                | exact resolve b25e22480 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e22480
              have b25e23707 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                intro X0
                first
                | (have j0 := b25e23561 X0
                   grind)
                | (have r₁ := b25e23561 X0
                   have r₂ := b25e22
                   grind)
                | exact resolve b25e23561 b25e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e23561
              have b25e38337 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e6361
                   have i₂ := b25e23707 (σ (M.op x y))
                   grind)
                | exact superpose b25e23707 b25e6361
                | exact resolve b25e6361 b25e23707
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6361 b25e23707
              have b25e38489 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b25e38337
                   have r₂ := b25e913
                   grind)
                | exact resolve b25e38337 b25e913
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e913 b25e38337
              have b25e40060 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b25e304 x (σ y)
                   have i₂ := b25e38489
                   grind)
                | exact superpose b25e38489 b25e304
                | (have j0 := b25e304 x (σ y)
                   grind)
                | (have r₁ := b25e304 x (σ y)
                   have r₂ := b25e38489
                   grind)
                | exact resolve b25e304 b25e38489
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e304 b25e38489
              have b25e40132 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by grind
              clear b25e40060
              have b25e40149 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
                first
                | (have i₁ := b25e40132
                   have i₂ := b25e21 y x
                   grind)
                | exact superpose b25e21 b25e40132
                | exact resolve b25e40132 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e40132
              have b25e40169 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e40149
                   have i₂ := b25e237
                   grind)
                | exact superpose b25e237 b25e40149
                | exact resolve b25e40149 b25e237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e237 b25e40149
              have b25e40182 : (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e40169
                   have i₂ := b25e89 y
                   grind)
                | exact superpose b25e89 b25e40169
                | exact resolve b25e40169 b25e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e89 b25e40169
              have b25e40194 : (σ (M.op x y)) = (σ y) := by
                first
                | (have i₁ := b25e40182
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e40182
                | exact resolve b25e40182 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e40182
              have b25e41687 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e2525 x y x
                   have i₂ := b25e40194
                   grind)
                | exact superpose b25e40194 b25e2525
                | exact resolve b25e2525 b25e40194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2525
              have b25e48254 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e41687 (σ x)
                   grind)
                | exact superpose b25e41687 b25e22
                | exact resolve b25e22 b25e41687
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e41687
              have b25e48305 : False := by grind
              exact b25e48305
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e27 : (M.op x y) ≠ (M.op x x) := by grind
              have b26e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b26e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e36 X0 X1 x X3
                   have i₂ := b26e15 X0 X1 x
                   grind)
                | exact superpose b26e15 b26e36
                | exact resolve b26e36 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e36
              have b26e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 X0
                   have i₂ := b26e69 (σ X0)
                   grind)
                | exact superpose b26e69 b26e21
                | exact resolve b26e21 b26e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e76 X0
                   have i₂ := b26e69 X0
                   grind)
                | exact superpose b26e69 b26e76
                | exact resolve b26e76 b26e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e69 b26e76
              have b26e140 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e19 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e19
                | (have j0 := b26e19 X0 X1
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e19 X1 X1
                   have r₂ := b26e20 X1 X1
                   grind)
                | (have r₁ := b26e19 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | (have r₁ := b26e19 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | exact resolve b26e19 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e158 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e161 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e20 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e163 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e140 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e140
              have b26e166 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e158 X0 X1
                   have i₂ := b26e81 X0
                   grind)
                | exact superpose b26e81 b26e158
                | (have j0 := b26e158 X0 X1
                   grind)
                | exact resolve b26e158 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e158
              have b26e168 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b26e163 X0 X1
                   have j1 := b26e161 X1 X0
                   grind)
                | (have r₁ := b26e163 X0 X1
                   have r₂ := b26e161 X0 X1
                   grind)
                | (have r₁ := b26e163 X1 X0
                   have r₂ := b26e161 X0 X1
                   grind)
                | (have r₁ := b26e163 X0 X0
                   have r₂ := b26e161 X0 X0
                   grind)
                | exact resolve b26e163 b26e161
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e161 b26e163
              have b26e177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e166 X0 X1
                   have i₂ := b26e81 X1
                   grind)
                | exact superpose b26e81 b26e166
                | (have j0 := b26e166 X0 X1
                   grind)
                | exact resolve b26e166 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e166
              have b26e198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e168 (σ X0) (σ X1)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e168
                | (have j0 := b26e168 (σ X0) (σ X1)
                   grind)
                | exact resolve b26e168 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e168
              have b26e242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e198 X0 X1
                   have i₂ := b26e81 X1
                   grind)
                | exact superpose b26e81 b26e198
                | (have j0 := b26e198 X0 X1
                   grind)
                | exact resolve b26e198 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e198
              have b26e292 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 (σ X0)
                   have i₂ := b26e81 X0
                   grind)
                | exact superpose b26e81 b26e18
                | (have j0 := b26e18 X1 (σ X0)
                   grind)
                | exact resolve b26e18 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e683 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e177 x y
                   grind)
                | exact superpose b26e177 b26e22
                | (have j1 := b26e177 x y
                   grind)
                | exact resolve b26e22 b26e177
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e177
              have b26e8052 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 (σ X0) (σ X1)
                   have i₂ := b26e242 X0 X1
                   grind)
                | exact superpose b26e242 b26e19
                | (have j0 := b26e19 (σ X0) (σ X1)
                   have j1 := b26e242 X0 X1
                   grind)
                | exact resolve b26e19 b26e242
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e8179 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
                intro X0 X1
                first
                | (have j0 := b26e242 X1 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e8235 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e8052 X0 X1
                   have i₂ := b26e81 X0
                   grind)
                | exact superpose b26e81 b26e8052
                | (have j0 := b26e8052 X0 X1
                   grind)
                | exact resolve b26e8052 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8052
              have b26e8349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e8235 X0 X1
                   have i₂ := b26e81 X1
                   grind)
                | exact superpose b26e81 b26e8235
                | (have j0 := b26e8235 X0 X1
                   grind)
                | exact resolve b26e8235 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8235
              have b26e8421 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have j0 := b26e8349 X0 X1
                   have j1 := b26e8179 X1 X0
                   grind)
                | (have r₁ := b26e8349 X1 X0
                   have r₂ := b26e8179 X0 X1
                   grind)
                | (have r₁ := b26e8349 (M.op X0 X0) X0
                   have r₂ := b26e8179 X0 (M.op X0 X0)
                   grind)
                | exact resolve b26e8349 b26e8179
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8179 b26e8349
              have b26e8462 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e8421 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e8421
                | (have j0 := b26e8421 X0 X1
                   grind)
                | exact resolve b26e8421 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8421
              have b26e8463 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have j0 := b26e8462 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8462
              have b26e14617 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b26e683
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e683
                | (have j1 := b26e20 y x
                   grind)
                | exact resolve b26e683 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e683
              have b26e14634 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
              clear b26e14617
              have b26e14643 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have r₁ := b26e14634
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e14634 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e14634
              have b26e14644 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b26e14643
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e14643 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e14643
              have b26e107342 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e242 y x
                   have i₂ := b26e14644
                   grind)
                | exact superpose b26e14644 b26e242
                | (have j0 := b26e242 y x
                   grind)
                | exact resolve b26e242 b26e14644
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e242
              have b26e107381 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
              clear b26e14644
              have b26e107400 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have j1 := b26e8463 y x
                   grind)
                | (have r₁ := b26e107342
                   have r₂ := b26e8463 y x
                   grind)
                | exact resolve b26e107342 b26e8463
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e8463 b26e107342
              have b26e107409 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have r₁ := b26e107400
                   have r₂ := b26e107381
                   grind)
                | exact resolve b26e107400 b26e107381
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e107381 b26e107400
              have b26e109218 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e292 x (σ y)
                   have i₂ := b26e107409
                   grind)
                | exact superpose b26e107409 b26e292
                | (have j0 := b26e292 x (σ y)
                   grind)
                | (have r₁ := b26e292 x (σ y)
                   have r₂ := b26e107409
                   grind)
                | exact resolve b26e292 b26e107409
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e292 b26e107409
              have b26e109259 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by grind
              clear b26e109218
              have b26e109277 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e109259
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e109259
                | exact resolve b26e109259 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e109259
              have b26e109284 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e109277
                   have i₂ := b26e81 y
                   grind)
                | exact superpose b26e81 b26e109277
                | exact resolve b26e109277 b26e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e81 b26e109277
              have b26e114971 : (k y x) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e16 (k y x)
                   have i₂ := b26e109284
                   grind)
                | exact superpose b26e109284 b26e16
                | exact resolve b26e16 b26e109284
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e109284
              have b26e115030 : (σ y) = (σ (k y x)) ∨ (M.op y y) = (k y x) := by
                first
                | (have i₁ := b26e114971
                   have i₂ := b26e16 (M.op y y)
                   grind)
                | exact superpose b26e16 b26e114971
                | exact resolve b26e114971 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e114971
              have b26e115553 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
                first
                | (have i₁ := b26e115030
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e115030
                | (have j1 := b26e20 y x
                   grind)
                | exact resolve b26e115030 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e115030
              have b26e115651 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
              clear b26e115553
              have b26e115693 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
                first
                | (have r₁ := b26e115651
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e115651 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e115651
              have b26e115702 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b26e115693
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e115693 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e115693
              have b26e116027 : (M.op x y) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (M.op x y)
                   have i₂ := b26e115702
                   grind)
                | exact superpose b26e115702 b26e16
                | exact resolve b26e16 b26e115702
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e115702
              have b26e116151 : y = (M.op x y) := by
                first
                | (have i₁ := b26e116027
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e116027
                | exact resolve b26e116027 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e116027
              have b26e116526 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e37 x y x
                   have i₂ := b26e116151
                   grind)
                | exact superpose b26e116151 b26e37
                | exact resolve b26e37 b26e116151
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e37
              have b26e116973 : y ≠ (M.op x y) := by
                first
                | (have i₁ := b26e28
                   have i₂ := b26e116526 y
                   grind)
                | exact superpose b26e116526 b26e28
                | exact resolve b26e28 b26e116526
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e116526
              have b26e116988 : False := by grind
              exact b26e116988

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_y_x_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e22 : y = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b0e36 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b0e12 x y x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b0e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e38 X0 X1 x X3
             have i₂ := b0e12 X0 X1 x
             grind)
          | exact superpose b0e12 b0e38
          | exact resolve b0e38 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e46 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 (M.op y y) X1
             have i₂ := b0e36 (M.op X0 (M.op y y))
             grind)
          | exact superpose b0e36 b0e12
          | exact resolve b0e12 b0e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b0e46 x X1
             have i₂ := b0e36 x
             grind)
          | exact superpose b0e36 b0e46
          | exact resolve b0e46 b0e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36 b0e46
        have b0e67 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e15 y X0
             have i₂ := b0e47 X0
             grind)
          | exact superpose b0e47 b0e15
          | (have j0 := b0e15 y X0
             grind)
          | (have r₁ := b0e15 y x
             have r₂ := b0e47 x
             grind)
          | exact resolve b0e15 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e70 : ∀ X0 : G, (k y X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e67 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e67
        have b0e103 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1 x
             have i₂ := b0e40 (M.op X0 X1) X1 x
             grind)
          | exact superpose b0e40 b0e12
          | exact resolve b0e12 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e134 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e33 X0 y
             have i₂ := b0e70 (τ X0)
             grind)
          | exact superpose b0e70 b0e33
          | exact resolve b0e33 b0e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33 b0e70
        have b0e142 : ∀ X0 : G, (k (σ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e134 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e134
          | exact resolve b0e134 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e134
        have b0e148 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear b0e142
        have b0e152 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e148
             have i₂ := b0e103 (σ y) (σ y)
             grind)
          | exact superpose b0e103 b0e148
          | exact resolve b0e148 b0e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e103 b0e148
        have b0e153 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b0e152
        have b0e502 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e40 (σ y) (σ y) x
             have i₂ := b0e153
             grind)
          | exact superpose b0e153 b0e40
          | exact resolve b0e40 b0e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40 b0e153
        have b0e566 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e502 (σ x)
             grind)
          | exact superpose b0e502 b0e24
          | (have r₁ := b0e24
             have r₂ := b0e502 (σ x)
             grind)
          | exact resolve b0e24 b0e502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e502
        have b0e568 : False := by grind
        exact b0e568
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e23 : y ≠ (M.op x y) := by grind
          have b1e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b1e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 (τ X0)
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b1e13 y y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b1e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e38 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e38
            | exact resolve b1e38 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38
          have b1e47 : y = (k y x) ∨ y = (M.op x y) := by grind
          have b1e50 : y = (k y x) := by
            first
            | (have r₁ := b1e47
               have r₂ := b1e23
               grind)
            | exact resolve b1e47 b1e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47
          have b1e56 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e18 X1 X2
               have i₂ := b1e18 X1 X0
               grind)
            | (have i₁ := b1e18 X0 X1
               have i₂ := b1e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b1e18 b1e18
            | (have j0 := b1e18 X1 X2
               have j1 := b1e18 X1 X2
               grind)
            | exact resolve b1e18 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 X0
               have i₂ := b1e18 (σ X1) (σ X0)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X0)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e101 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 X1 x
               have i₂ := b1e40 (M.op X0 X1) X1 x
               grind)
            | exact superpose b1e40 b1e13
            | exact resolve b1e13 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e103 : x = (M.op x y) := by
            first
            | (have i₁ := b1e35 x
               have i₂ := b1e40 x y x
               grind)
            | exact superpose b1e40 b1e35
            | exact resolve b1e35 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35 b1e40
          have b1e113 : x ≠ y := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e103
               grind)
            | exact superpose b1e103 b1e23
            | exact resolve b1e23 b1e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e119 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            grind
          have b1e123 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b1e14 (k (τ X0) X1)
               have i₂ := b1e32 X0 X1
               grind)
            | exact superpose b1e32 b1e14
            | exact resolve b1e14 b1e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32
          have b1e124 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e119 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e119
            | (have j0 := b1e119 X0
               grind)
            | exact resolve b1e119 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e119
          have b1e125 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e124 X0
               have i₂ := b1e101 (τ X0) (τ X0)
               grind)
            | exact superpose b1e101 b1e124
            | (have j0 := b1e124 X0
               grind)
            | exact resolve b1e124 b1e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e124
          have b1e127 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e33 X0 X1
               have i₂ := b1e18 X1 (τ X0)
               grind)
            | exact superpose b1e18 b1e33
            | (have j1 := b1e18 X1 (τ X0)
               grind)
            | exact resolve b1e33 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e368 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b1e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e57
          have b1e421 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e16 X1 (M.op X0 X1)
               have i₂ := b1e101 X0 X1
               grind)
            | exact superpose b1e101 b1e16
            | (have j0 := b1e16 X1 X0
               grind)
            | exact resolve b1e16 b1e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e477 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (k y X0) ∨ x = X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b1e50
               have i₂ := b1e56 x y X0
               grind)
            | exact superpose b1e56 b1e50
            | (have j1 := b1e56 X0 y X0
               grind)
            | exact resolve b1e50 b1e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e56
          have b1e482 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (k y X0) ∨ x = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b1e477 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e477
          have b1e490 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b1e482 X0
               grind)
            | (have r₁ := b1e482 X0
               have r₂ := b1e23
               grind)
            | (have r₁ := b1e482 x
               have r₂ := b1e23
               grind)
            | exact resolve b1e482 b1e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e482
          have b1e535 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e123 X2 (k X0 (τ X1))
               have i₂ := b1e33 X1 X0
               grind)
            | exact superpose b1e33 b1e123
            | exact resolve b1e123 b1e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e33 b1e123
          have b1e1594 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e125 X0
               have i₂ := b1e127 X0 (τ X0)
               grind)
            | exact superpose b1e127 b1e125
            | (have j0 := b1e125 X0
               have j1 := b1e127 X0 (τ X0)
               grind)
            | exact resolve b1e125 b1e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e125 b1e127
          have b1e1655 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b1e1594 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1594
          have b1e1680 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e1655 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e1655
            | (have j0 := b1e1655 X0
               grind)
            | exact resolve b1e1655 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1655
          have b1e2114 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e368 x y
               have i₂ := b1e50
               grind)
            | exact superpose b1e50 b1e368
            | (have j0 := b1e368 x y
               grind)
            | exact resolve b1e368 b1e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e50 b1e368
          have b1e2119 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b1e2114
          have b1e15080 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b1e535 X0 (σ X0) (σ X0)
               have i₂ := b1e1680 (σ X0)
               grind)
            | exact superpose b1e1680 b1e535
            | (have j1 := b1e1680 (σ X0)
               grind)
            | exact resolve b1e535 b1e1680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e535 b1e1680
          have b1e15194 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b1e15080 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e15080
            | (have j0 := b1e15080 X0
               grind)
            | exact resolve b1e15080 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15080
          have b1e15225 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e15194 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e15194
            | (have j0 := b1e15194 X0
               grind)
            | exact resolve b1e15194 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15194
          have b1e15431 : y = (M.op (k y y) y) ∨ x = (k y y) ∨ y = (M.op (k y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b1e490 (k y y)
               have i₂ := b1e15225 y
               grind)
            | exact superpose b1e15225 b1e490
            | (have j0 := b1e490 (k y y)
               have j1 := b1e15225 y
               grind)
            | exact resolve b1e490 b1e15225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e490 b1e15225
          have b1e15432 : y = (M.op (k y y) y) ∨ x = (k y y) ∨ y = (M.op y y) := by grind
          clear b1e15431
          have b1e15470 : x = y ∨ y = (M.op (k y y) y) ∨ x = (k y y) := by
            first
            | (have i₁ := b1e15432
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e15432
            | exact resolve b1e15432 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15432
          have b1e15505 : y = (M.op (k y y) y) ∨ x = (k y y) := by
            first
            | (have r₁ := b1e15470
               have r₂ := b1e113
               grind)
            | exact resolve b1e15470 b1e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15470
          have b1e15600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e101 (σ y) (σ y)
               have i₂ := b1e2119
               grind)
            | exact superpose b1e2119 b1e101
            | exact resolve b1e101 b1e2119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e2119
          have b1e15659 : y = (M.op y y) ∨ x = (k y y) := by
            first
            | (have i₁ := b1e101 (k y y) y
               have i₂ := b1e15505
               grind)
            | exact superpose b1e15505 b1e101
            | exact resolve b1e101 b1e15505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e101 b1e15505
          have b1e15684 : x = y ∨ x = (k y y) := by
            first
            | (have i₁ := b1e15659
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e15659
            | exact resolve b1e15659 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15659
          have b1e15686 : x = (k y y) := by
            first
            | (have r₁ := b1e15684
               have r₂ := b1e113
               grind)
            | exact resolve b1e15684 b1e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e113 b1e15684
          have b1e41786 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e421 (σ x) (σ y)
               have i₂ := b1e15600
               grind)
            | exact superpose b1e15600 b1e421
            | (have r₁ := b1e421 (σ x) (σ y)
               have r₂ := b1e15600
               grind)
            | exact resolve b1e421 b1e15600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e421
          have b1e41810 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b1e15600
          have b1e41811 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b1e41786
          have b1e41826 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e41811
               have i₂ := b1e19 y y
               grind)
            | exact superpose b1e19 b1e41811
            | exact resolve b1e41811 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41811
          have b1e41833 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e41826
               have i₂ := b1e15686
               grind)
            | exact superpose b1e15686 b1e41826
            | exact resolve b1e41826 b1e15686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15686 b1e41826
          have b1e41835 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b1e41833
               have r₂ := b1e41810
               grind)
            | exact resolve b1e41833 b1e41810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41810 b1e41833
          have b1e42391 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e41835
               grind)
            | exact superpose b1e41835 b1e20
            | exact resolve b1e20 b1e41835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41835
          have b1e42470 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e42391
               have i₂ := b1e103
               grind)
            | exact superpose b1e103 b1e42391
            | exact resolve b1e42391 b1e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e103 b1e42391
          have b1e42471 : False := by grind
          exact b1e42471
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e23 : y ≠ (M.op x y) := by grind
          have b2e24 : x ≠ (M.op y y) := by grind
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
          have b2e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b2e31
          have b2e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b2e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e40 X0 X1 x X3
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e40
            | exact resolve b2e40 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40
          have b2e68 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e73 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e68
          have b2e85 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 X0 X0 x
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e42 X0 X1 x
               have i₂ := b2e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b2e18 b2e42
            | (have j1 := b2e18 X1 X0
               grind)
            | exact resolve b2e42 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e94 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e16 (M.op X0 X1) X2
               have i₂ := b2e42 X0 X1 X2
               grind)
            | exact superpose b2e42 b2e16
            | (have j0 := b2e16 (M.op X0 X1) X2
               grind)
            | (have r₁ := b2e16 (M.op X0 X1) x
               have r₂ := b2e42 X0 X1 x
               grind)
            | exact resolve b2e16 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e96 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e94 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e94
          have b2e110 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e32 X0 X1
               have i₂ := b2e18 X1 (τ X0)
               grind)
            | exact superpose b2e18 b2e32
            | (have j1 := b2e18 X1 (τ X0)
               grind)
            | exact resolve b2e32 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32
          have b2e156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e73 (σ X1) (σ X0)
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e73
            | (have j0 := b2e73 (σ X1) (σ X0)
               grind)
            | exact resolve b2e73 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73
          have b2e503 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e36 (M.op X1 X2) X0
               have i₂ := b2e96 X1 X2 (σ X0)
               grind)
            | exact superpose b2e96 b2e36
            | exact resolve b2e36 b2e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e96
          have b2e523 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e503 X0 X1 X2
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e503
            | exact resolve b2e503 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e503
          have b2e1205 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X1 X0 X2
               have i₂ := b2e85 X0 X3 (M.op X1 X0)
               grind)
            | exact superpose b2e85 b2e13
            | (have j1 := b2e85 X0 X3 X2
               grind)
            | exact resolve b2e13 b2e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e1458 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e110 (σ X0) X1
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e110
            | exact resolve b2e110 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e110
          have b2e1557 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e1458 X0 X1
               have i₂ := b2e19 X1 X0
               grind)
            | exact superpose b2e19 b2e1458
            | (have j0 := b2e1458 X0 X1
               grind)
            | exact resolve b2e1458 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1458
          have b2e2399 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e156 y x
               grind)
            | exact superpose b2e156 b2e20
            | (have j1 := b2e156 y x
               grind)
            | exact resolve b2e20 b2e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e156
          have b2e17300 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (k X1 y) = (M.op y X1) ∨ (M.op y X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e23
               have i₂ := b2e1205 y x X0 X1
               grind)
            | (have i₁ := b2e23
               have i₂ := b2e1205 y X0 x X1
               grind)
            | exact superpose b2e1205 b2e23
            | (have j1 := b2e1205 y X1 x X1
               grind)
            | (have r₁ := b2e23
               have r₂ := b2e1205 x X1 x y
               grind)
            | exact resolve b2e23 b2e1205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1205
          have b2e17438 : ∀ X1 : G, (k X1 y) = (M.op y X1) ∨ (M.op y X1) = X1 := by
            intro X1
            first
            | (have j0 := b2e17300 x X1
               have j1 := b2e85 y X1 x
               grind)
            | (have r₁ := b2e17300 x X1
               have r₂ := b2e85 y X1 x
               grind)
            | (have r₁ := b2e17300 x X1
               have r₂ := b2e85 x y x
               grind)
            | exact resolve b2e17300 b2e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e85 b2e17300
          have b2e72364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e2399
               have i₂ := b2e1557 x y
               grind)
            | exact superpose b2e1557 b2e2399
            | (have j1 := b2e1557 x y
               grind)
            | (have r₁ := b2e2399
               have r₂ := b2e1557 x y
               grind)
            | exact resolve b2e2399 b2e1557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1557 b2e2399
          have b2e72373 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b2e72364
          have b2e72384 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b2e72373
               have r₂ := b2e24
               grind)
            | exact resolve b2e72373 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e72373
          have b2e72391 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b2e72384
               have r₂ := b2e23
               grind)
            | exact resolve b2e72384 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e72384
          have b2e72417 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e523 X0 (σ x) (σ y)
               have i₂ := b2e72391
               grind)
            | exact superpose b2e72391 b2e523
            | exact resolve b2e523 b2e72391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e523 b2e72391
          have b2e72456 : ∀ X0 : G, (k y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e72417 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e72417
            | exact resolve b2e72417 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e72417
          have b2e73215 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e72456 X0
               grind)
            | exact superpose b2e72456 b2e14
            | (have j1 := b2e72456 X0
               grind)
            | exact resolve b2e14 b2e72456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e72456
          have b2e73371 : ∀ X0 : G, y = (M.op x y) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e73215 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e73215
            | (have j0 := b2e73215 X0
               grind)
            | exact resolve b2e73215 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73215
          have b2e73408 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e73371 X0
               grind)
            | (have r₁ := b2e73371 X0
               have r₂ := b2e23
               grind)
            | exact resolve b2e73371 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73371
          have b2e74526 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b2e17438 y
               have i₂ := b2e73408 y
               grind)
            | exact superpose b2e73408 b2e17438
            | (have j0 := b2e17438 y
               grind)
            | exact resolve b2e17438 b2e73408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e17438 b2e73408
          have b2e74527 : y = (M.op y y) := by grind
          clear b2e74526
          have b2e75349 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e42 y y x
               have i₂ := b2e74527
               grind)
            | exact superpose b2e74527 b2e42
            | exact resolve b2e42 b2e74527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e42 b2e74527
          have b2e75770 : y ≠ y := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e75349 x
               grind)
            | exact superpose b2e75349 b2e23
            | (have r₁ := b2e23
               have r₂ := b2e75349 x
               grind)
            | exact resolve b2e23 b2e75349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e75349
          have b2e75772 : False := by grind
          exact b2e75772
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : x = (M.op y x) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e27 : x ≠ x ∨ y = (k x y) := by
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
          have b3e31 : y = (k x y) := by grind
          clear b3e27
          have b3e50 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          have b3e51 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e50
               have r₂ := b3e22
               grind)
            | exact resolve b3e50 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e50
          have b3e52 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e51
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e51
            | exact resolve b3e51 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e51
          have b3e53 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e52
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e52
            | exact resolve b3e52 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e52
          have b3e55 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e53
               grind)
            | exact superpose b3e53 b3e22
            | exact resolve b3e22 b3e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e62 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e55
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e55
            | exact resolve b3e55 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e55
          have b3e64 : False := by grind
          exact b3e64
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : x ≠ x ∨ y = (k x y) := by
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
            have b4e31 : y = (k x y) := by grind
            clear b4e28
            have b4e53 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b4e58 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e53
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e53 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e53
            have b4e60 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b4e58
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e58
              | exact resolve b4e58 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e58
            have b4e61 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e60
                 have i₂ := b4e31
                 grind)
              | exact superpose b4e31 b4e60
              | exact resolve b4e60 b4e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e31 b4e60
            have b4e86 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e61
                 grind)
              | exact superpose b4e61 b4e23
              | exact resolve b4e23 b4e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e93 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e86
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e86
              | exact resolve b4e86 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e86
            have b4e95 : False := by grind
            exact b4e95
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : x = (M.op y x) := by grind
            have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : x ≠ x ∨ y = (k x y) := by
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
            have b5e30 : y = (k x y) := by grind
            clear b5e28
            have b5e46 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b5e49 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e46
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e46 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e46
            have b5e50 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e49
              | exact resolve b5e49 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e49
            have b5e51 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e50
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e50
              | exact resolve b5e50 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e50
            have b5e53 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e51
                 grind)
              | exact superpose b5e51 b5e23
              | exact resolve b5e23 b5e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e60 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e53
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e53
              | exact resolve b5e53 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e53
            have b5e62 : False := by grind
            exact b5e62
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
          have b6e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e20
            | exact resolve b6e20 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e27 : x ≠ x ∨ y = (k x y) := by
            first
            | (have i₁ := b6e16 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 x y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e30 : y = (k x y) := by grind
          clear b6e27
          have b6e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b6e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e36 X0 X1 x X3
               have i₂ := b6e13 X0 X1 x
               grind)
            | exact superpose b6e13 b6e36
            | exact resolve b6e36 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e36
          have b6e68 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e23
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e317 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b6e68 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e68
          have b6e318 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e317
               have r₂ := b6e22
               grind)
            | exact resolve b6e317 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e317
          have b6e319 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e318
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e318
            | exact resolve b6e318 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e318
          have b6e320 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b6e319
               have i₂ := b6e30
               grind)
            | exact superpose b6e30 b6e319
            | exact resolve b6e319 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e319
          have b6e325 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e38 (σ y) (σ x) x
               have i₂ := b6e320
               grind)
            | exact superpose b6e320 b6e38
            | exact resolve b6e38 b6e320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38 b6e320
          have b6e483 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e26
               have i₂ := b6e325 (σ x)
               grind)
            | exact superpose b6e325 b6e26
            | (have r₁ := b6e26
               have r₂ := b6e325 (σ x)
               grind)
            | exact resolve b6e26 b6e325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e325
          have b6e485 : False := by grind
          exact b6e485
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b7e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : x = (M.op y x) := by grind
            have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e25 : y ≠ (M.op x y) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : x ≠ x ∨ y = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 x y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e30 : y = (k x y) := by grind
            clear b7e28
            have b7e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 (τ X0) X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b7e15 (k (τ X0) X1)
                 have i₂ := b7e31 X0 X1
                 grind)
              | exact superpose b7e31 b7e15
              | exact resolve b7e15 b7e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31
            have b7e38 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b7e14 y y x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b7e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b7e40 X0 X1 x X3
                 have i₂ := b7e14 X0 X1 x
                 grind)
              | exact superpose b7e14 b7e40
              | exact resolve b7e40 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e49 : y = (k y x) ∨ y = (M.op x y) := by grind
            have b7e54 : y = (k y x) := by
              first
              | (have r₁ := b7e49
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e49 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e49
            have b7e70 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e24
                 have i₂ := b7e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b7e19 b7e24
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e24
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e24 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e108 : x = (M.op x y) := by
              first
              | (have i₁ := b7e38 x
                 have i₂ := b7e42 x y x
                 grind)
              | exact superpose b7e42 b7e38
              | exact resolve b7e38 b7e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e112 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e17 (M.op X0 X1) X2
                 have i₂ := b7e42 X0 X1 X2
                 grind)
              | exact superpose b7e42 b7e17
              | (have j0 := b7e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b7e17 (M.op X0 X1) x
                 have r₂ := b7e42 X0 X1 x
                 grind)
              | exact resolve b7e17 b7e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e42
            have b7e114 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b7e112 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e112
            have b7e118 : x ≠ y := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e108
                 grind)
              | exact superpose b7e108 b7e25
              | exact resolve b7e25 b7e108
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e108
            have b7e268 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e70 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e70
            have b7e269 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e268
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e268 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e268
            have b7e270 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e269
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e269
              | exact resolve b7e269 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e269
            have b7e271 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e270
                 have i₂ := b7e30
                 grind)
              | exact superpose b7e30 b7e270
              | exact resolve b7e270 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e30 b7e270
            have b7e275 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e114 (σ y) (σ x) X0
                 have i₂ := b7e271
                 grind)
              | exact superpose b7e271 b7e114
              | exact resolve b7e114 b7e271
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e114 b7e271
            have b7e503 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b7e36 (σ y) X0
                 have i₂ := b7e275 (σ X0)
                 grind)
              | exact superpose b7e275 b7e36
              | exact resolve b7e36 b7e275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e275
            have b7e511 : ∀ X0 : G, (τ (σ X0)) = (k y X0) := by
              intro X0
              first
              | (have i₁ := b7e503 X0
                 have i₂ := b7e15 y
                 grind)
              | exact superpose b7e15 b7e503
              | exact resolve b7e503 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e503
            have b7e517 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e511 X0
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e511
              | exact resolve b7e511 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e511
            have b7e527 : x = y := by
              first
              | (have i₁ := b7e54
                 have i₂ := b7e517 x
                 grind)
              | exact superpose b7e517 b7e54
              | exact resolve b7e54 b7e517
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e54 b7e517
            have b7e542 : False := by grind
            exact b7e542
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : x = (M.op y x) := by grind
            have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 X1 (τ X0)
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e32 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b8e14 y x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b8e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e34 X0 X1 x X3
                 have i₂ := b8e14 X0 X1 x
                 grind)
              | exact superpose b8e14 b8e34
              | exact resolve b8e34 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e34
            have b8e40 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 (M.op x x) X1
                 have i₂ := b8e32 (M.op X0 (M.op x x))
                 grind)
              | exact superpose b8e32 b8e14
              | exact resolve b8e14 b8e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e41 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b8e40 x X1
                 have i₂ := b8e32 x
                 grind)
              | exact superpose b8e32 b8e40
              | exact resolve b8e40 b8e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32 b8e40
            have b8e47 : ∀ X0 : G, x ≠ x ∨ (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e17 x X0
                 have i₂ := b8e41 X0
                 grind)
              | exact superpose b8e41 b8e17
              | (have j0 := b8e17 x X0
                 grind)
              | (have r₁ := b8e17 x x
                 have r₂ := b8e41 x
                 grind)
              | exact resolve b8e17 b8e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41
            have b8e50 : ∀ X0 : G, (k x X0) = X0 := by
              intro X0
              first
              | (have j0 := b8e47 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e47
            have b8e80 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 X1 x
                 have i₂ := b8e36 (M.op X0 X1) X1 x
                 grind)
              | exact superpose b8e36 b8e14
              | exact resolve b8e14 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e131 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b8e31 X0 x
                 have i₂ := b8e50 (τ X0)
                 grind)
              | exact superpose b8e50 b8e31
              | exact resolve b8e31 b8e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31 b8e50
            have b8e139 : ∀ X0 : G, (k (σ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e131 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e131
              | exact resolve b8e131 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e131
            have b8e145 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
            clear b8e139
            have b8e149 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b8e145
                 have i₂ := b8e80 (σ x) (σ x)
                 grind)
              | exact superpose b8e80 b8e145
              | exact resolve b8e145 b8e80
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e80 b8e145
            have b8e150 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b8e149
            have b8e258 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b8e36 (σ x) (σ x) x
                 have i₂ := b8e150
                 grind)
              | exact superpose b8e150 b8e36
              | exact resolve b8e36 b8e150
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36 b8e150
            have b8e280 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e258 (σ y)
                 grind)
              | exact superpose b8e258 b8e23
              | (have r₁ := b8e23
                 have r₂ := b8e258 (σ y)
                 grind)
              | exact resolve b8e23 b8e258
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e258
            have b8e282 : False := by grind
            exact b8e282
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : x ≠ (M.op y x) := by grind
          have b9e22 : y = (M.op x x) := by grind
          have b9e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          have b9e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e20
            | exact resolve b9e20 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ y)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e30 : (σ y) = (k (σ x) (σ y)) := by grind
          clear b9e29
          have b9e32 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e30
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e30
            | exact resolve b9e30 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30
          have b9e37 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e32
               grind)
            | exact superpose b9e32 b9e14
            | exact resolve b9e14 b9e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e38 : y = (k x y) := by
            first
            | (have i₁ := b9e37
               have i₂ := b9e14 y
               grind)
            | exact superpose b9e14 b9e37
            | exact resolve b9e37 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e49 : x = (k x y) ∨ x = (M.op y x) := by grind
          have b9e51 : x = (k x y) := by
            first
            | (have r₁ := b9e49
               have r₂ := b9e21
               grind)
            | exact resolve b9e49 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e49
          have b9e53 : x = y := by
            first
            | (have i₁ := b9e38
               have i₂ := b9e51
               grind)
            | exact superpose b9e51 b9e38
            | exact resolve b9e38 b9e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e38 b9e51
          have b9e75 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e23
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e23
            | exact resolve b9e23 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e77 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e26
            | exact resolve b9e26 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26 b9e53
          have b9e82 : False := by grind
          exact b9e82
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : x ≠ (M.op y x) := by grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : y ≠ (M.op x y) := by grind
            have b10e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e30 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b10e30
            have b10e32 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b10e31
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e31
              | exact resolve b10e31 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e31
            have b10e33 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e32
                 grind)
              | exact superpose b10e32 b10e15
              | exact resolve b10e15 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e34 : y = (k x y) := by
              first
              | (have i₁ := b10e33
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e33
              | exact resolve b10e33 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e56 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b10e58 : x = (k x y) := by
              first
              | (have r₁ := b10e56
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e56 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e56
            have b10e60 : x = y := by
              first
              | (have i₁ := b10e34
                 have i₂ := b10e58
                 grind)
              | exact superpose b10e58 b10e34
              | exact resolve b10e34 b10e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34 b10e58
            have b10e84 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e60
                 grind)
              | exact superpose b10e60 b10e25
              | exact resolve b10e25 b10e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e85 : x = (M.op x x) := by
              first
              | (have i₁ := b10e26
                 have i₂ := b10e60
                 grind)
              | exact superpose b10e60 b10e26
              | exact resolve b10e26 b10e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e60
            have b10e93 : False := by grind
            exact b10e93
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : x ≠ (M.op y x) := by grind
            have b11e23 : y = (M.op x x) := by grind
            have b11e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b11e26 : x ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e30 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b11e29
            have b11e31 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e30
              | exact resolve b11e30 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e15
              | exact resolve b11e15 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e33 : y = (k x y) := by
              first
              | (have i₁ := b11e32
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e32
              | exact resolve b11e32 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e52 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b11e55 : x = (k x y) := by
              first
              | (have r₁ := b11e52
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e52 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e52
            have b11e57 : x = y := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e55
                 grind)
              | exact superpose b11e55 b11e33
              | exact resolve b11e33 b11e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33 b11e55
            have b11e82 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e57
                 grind)
              | exact superpose b11e57 b11e26
              | exact resolve b11e26 b11e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e90 : x ≠ y := by
              first
              | (have i₁ := b11e82
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e82
              | exact resolve b11e82 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e82
            have b11e94 : False := by grind
            exact b11e94
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b12e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b12e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e40 X0 X1 x X3
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e40
              | exact resolve b12e40 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e99 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e42 (σ x) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e42
              | exact resolve b12e42 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e166 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e99 (σ x)
                 grind)
              | exact superpose b12e99 b12e28
              | (have r₁ := b12e28
                 have r₂ := b12e99 (σ x)
                 grind)
              | exact resolve b12e28 b12e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e99
            have b12e174 : False := by grind
            exact b12e174
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e38 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b13e15 x x x
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e46 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 (M.op y x) X1
                   have i₂ := b13e38 (M.op X0 (M.op y x))
                   grind)
                | exact superpose b13e38 b13e15
                | exact resolve b13e15 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e47 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b13e46 x X1
                   have i₂ := b13e38 x
                   grind)
                | exact superpose b13e38 b13e46
                | exact resolve b13e46 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e38 b13e46
              have b13e76 : y ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e47 x
                   grind)
                | exact superpose b13e47 b13e27
                | (have r₁ := b13e27
                   have r₂ := b13e47 x
                   grind)
                | exact resolve b13e27 b13e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e47
              have b13e83 : False := by grind
              exact b13e83
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e39 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b14e15 x x x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e48 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (M.op y x) X1
                   have i₂ := b14e39 (M.op X0 (M.op y x))
                   grind)
                | exact superpose b14e39 b14e15
                | exact resolve b14e15 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e49 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b14e48 x X1
                   have i₂ := b14e39 x
                   grind)
                | exact superpose b14e39 b14e48
                | exact resolve b14e48 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39 b14e48
              have b14e79 : y ≠ y := by
                first
                | (have i₁ := b14e27
                   have i₂ := b14e49 x
                   grind)
                | exact superpose b14e49 b14e27
                | (have r₁ := b14e27
                   have r₂ := b14e49 x
                   grind)
                | exact resolve b14e27 b14e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e49
              have b14e86 : False := by grind
              exact b14e86
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : x ≠ (M.op y x) := by grind
            have b15e23 : y = (M.op x x) := by grind
            have b15e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e46 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b15e49 : x = (k x y) := by
              first
              | (have r₁ := b15e46
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e46 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e46
            have b15e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e272 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b15e64 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e64
            have b15e273 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e272
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e272 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e272
            have b15e274 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e273
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e273
              | exact resolve b15e273 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e273
            have b15e275 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e274
                 have i₂ := b15e49
                 grind)
              | exact superpose b15e49 b15e274
              | exact resolve b15e274 b15e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e49 b15e274
            have b15e276 : False := by grind
            exact b15e276
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b16e15 x x x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e43 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 (M.op y x) X1
                   have i₂ := b16e34 (M.op X0 (M.op y x))
                   grind)
                | exact superpose b16e34 b16e15
                | exact resolve b16e15 b16e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e44 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b16e43 x X1
                   have i₂ := b16e34 x
                   grind)
                | exact superpose b16e34 b16e43
                | exact resolve b16e43 b16e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34 b16e43
              have b16e69 : y ≠ y := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e44 x
                   grind)
                | exact superpose b16e44 b16e27
                | (have r₁ := b16e27
                   have r₂ := b16e44 x
                   grind)
                | exact resolve b16e27 b16e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e44
              have b16e76 : False := by grind
              exact b16e76
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e37 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b17e15 x x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e45 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 (M.op y x) X1
                   have i₂ := b17e37 (M.op X0 (M.op y x))
                   grind)
                | exact superpose b17e37 b17e15
                | exact resolve b17e15 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b17e45 x X1
                   have i₂ := b17e37 x
                   grind)
                | exact superpose b17e37 b17e45
                | exact resolve b17e45 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37 b17e45
              have b17e72 : y ≠ y := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e46 x
                   grind)
                | exact superpose b17e46 b17e27
                | (have r₁ := b17e27
                   have r₂ := b17e46 x
                   grind)
                | exact resolve b17e27 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e79 : False := by grind
              exact b17e79
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op y x) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e43 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b18e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e45 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e43 X0 X1 x X3
               have i₂ := b18e13 X0 X1 x
               grind)
            | exact superpose b18e13 b18e43
            | exact resolve b18e43 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43
          have b18e85 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e45 (σ y) (σ x) x
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e45
            | exact resolve b18e45 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 X1 x
               have i₂ := b18e45 (M.op X0 X1) X1 x
               grind)
            | exact superpose b18e45 b18e13
            | exact resolve b18e13 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e211 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e16 (σ x) X0
               have i₂ := b18e85 X0
               grind)
            | exact superpose b18e85 b18e16
            | (have j0 := b18e16 (σ x) X0
               grind)
            | (have r₁ := b18e16 (σ x) X0
               have r₂ := b18e85 X0
               grind)
            | exact resolve b18e16 b18e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e85
          have b18e213 : ∀ X0 : G, (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b18e211 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e211
          have b18e236 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e19 x X0
               have i₂ := b18e213 (σ X0)
               grind)
            | exact superpose b18e213 b18e19
            | exact resolve b18e19 b18e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e213
          have b18e366 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b18e14 (k x X0)
               have i₂ := b18e236 X0
               grind)
            | exact superpose b18e236 b18e14
            | exact resolve b18e14 b18e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e236
          have b18e375 : ∀ X0 : G, (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e366 X0
               have i₂ := b18e14 X0
               grind)
            | exact superpose b18e14 b18e366
            | exact resolve b18e366 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e366
          have b18e438 : x = (M.op x x) ∨ x = (M.op (M.op x x) x) := by grind
          clear b18e375
          have b18e448 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b18e438
               have i₂ := b18e94 x x
               grind)
            | exact superpose b18e94 b18e438
            | exact resolve b18e438 b18e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e94 b18e438
          have b18e449 : x = (M.op x x) := by grind
          clear b18e448
          have b18e490 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b18e45 x x x
               have i₂ := b18e449
               grind)
            | exact superpose b18e449 b18e45
            | exact resolve b18e45 b18e449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45 b18e449
          have b18e532 : x ≠ x := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e490 y
               grind)
            | exact superpose b18e490 b18e21
            | (have r₁ := b18e21
               have r₂ := b18e490 y
               grind)
            | exact resolve b18e21 b18e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e490
          have b18e545 : False := by grind
          exact b18e545
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e40 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b19e14 y y x
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e49 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 (M.op x y) X1
                 have i₂ := b19e40 (M.op X0 (M.op x y))
                 grind)
              | exact superpose b19e40 b19e14
              | exact resolve b19e14 b19e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e50 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b19e49 x X1
                 have i₂ := b19e40 x
                 grind)
              | exact superpose b19e40 b19e49
              | exact resolve b19e49 b19e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e40 b19e49
            have b19e75 : x ≠ x := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e50 y
                 grind)
              | exact superpose b19e50 b19e22
              | (have r₁ := b19e22
                 have r₂ := b19e50 y
                 grind)
              | exact resolve b19e22 b19e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e50
            have b19e82 : False := by grind
            exact b19e82
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e23 : y ≠ (M.op x x) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b20e25 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e29 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b20e28
            have b20e30 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e29
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e29
              | exact resolve b20e29 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e30
                 grind)
              | exact superpose b20e30 b20e15
              | exact resolve b20e15 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e32 : y = (k x y) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e31
              | exact resolve b20e31 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e45 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b20e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b20e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e47 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e45 X0 X1 x X3
                 have i₂ := b20e14 X0 X1 x
                 grind)
              | exact superpose b20e14 b20e45
              | exact resolve b20e45 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e45
            have b20e80 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e32
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e32
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e32 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e92 : y = (M.op y x) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b20e80
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e80 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e80
            have b20e95 : y = (M.op y x) := by
              first
              | (have r₁ := b20e92
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e92 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e92
            have b20e98 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b20e47 y x x
                 have i₂ := b20e95
                 grind)
              | exact superpose b20e95 b20e47
              | exact resolve b20e47 b20e95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e47 b20e95
            have b20e124 : y ≠ y := by
              first
              | (have i₁ := b20e25
                 have i₂ := b20e98 x
                 grind)
              | exact superpose b20e98 b20e25
              | (have r₁ := b20e25
                 have r₂ := b20e98 x
                 grind)
              | exact resolve b20e25 b20e98
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e98
            have b20e132 : False := by grind
            exact b20e132
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op y x) := by grind
            have b21e23 : y ≠ (M.op x x) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e47 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b21e50 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e47
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e47 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e47
            have b21e51 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e50
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e50
              | exact resolve b21e50 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e82 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e51
                 grind)
              | exact superpose b21e51 b21e15
              | exact resolve b21e15 b21e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e51
            have b21e83 : x = (k x y) := by
              first
              | (have i₁ := b21e82
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e82
              | exact resolve b21e82 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e82
            have b21e89 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e83
                 grind)
              | exact superpose b21e83 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e83
            have b21e90 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b21e89
            have b21e92 : y = (M.op x x) := by
              first
              | (have r₁ := b21e90
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e90 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e90
            have b21e94 : False := by grind
            exact b21e94
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b22e23 : x ≠ (M.op y x) := by grind
              have b22e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e39 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b22e15 y y x
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e48 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 (M.op x y) X1
                   have i₂ := b22e39 (M.op X0 (M.op x y))
                   grind)
                | exact superpose b22e39 b22e15
                | exact resolve b22e15 b22e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e49 : ∀ X1 : G, x = (M.op X1 x) := by
                intro X1
                first
                | (have i₁ := b22e48 x X1
                   have i₂ := b22e39 x
                   grind)
                | exact superpose b22e39 b22e48
                | exact resolve b22e48 b22e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39 b22e48
              have b22e79 : x ≠ x := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e49 y
                   grind)
                | exact superpose b22e49 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e49 y
                   grind)
                | exact resolve b22e23 b22e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e49
              have b22e86 : False := by grind
              exact b22e86
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : x ≠ (M.op y x) := by grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e51 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e54 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e51
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e51 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e51
              have b23e55 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e54
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e54
                | exact resolve b23e54 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e54
              have b23e58 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e55
                   grind)
                | exact superpose b23e55 b23e16
                | exact resolve b23e16 b23e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e55
              have b23e59 : x = (k x y) := by
                first
                | (have i₁ := b23e58
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e58
                | exact resolve b23e58 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e58
              have b23e81 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e59
                   grind)
                | exact superpose b23e59 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e59
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e59
              have b23e82 : x = (M.op y x) ∨ y = (M.op x x) := by grind
              clear b23e81
              have b23e84 : y = (M.op x x) := by
                first
                | (have r₁ := b23e82
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e82 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e82
              have b23e86 : False := by grind
              exact b23e86
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
              intro X0
              first
              | (have i₁ := b24e14 x y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b24e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b24e35 X0 X1 x X3
                 have i₂ := b24e14 X0 X1 x
                 grind)
              | exact superpose b24e14 b24e35
              | exact resolve b24e35 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e35
            have b24e41 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 (M.op y y) X1
                 have i₂ := b24e33 (M.op X0 (M.op y y))
                 grind)
              | exact superpose b24e33 b24e14
              | exact resolve b24e14 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e42 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b24e41 x X1
                 have i₂ := b24e33 x
                 grind)
              | exact superpose b24e33 b24e41
              | exact resolve b24e41 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33 b24e41
            have b24e49 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e17 y X0
                 have i₂ := b24e42 X0
                 grind)
              | exact superpose b24e42 b24e17
              | (have j0 := b24e17 y X0
                 grind)
              | (have r₁ := b24e17 y x
                 have r₂ := b24e42 x
                 grind)
              | exact resolve b24e17 b24e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42
            have b24e51 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have j0 := b24e49 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e49
            have b24e81 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 X1 x
                 have i₂ := b24e37 (M.op X0 X1) X1 x
                 grind)
              | exact superpose b24e37 b24e14
              | exact resolve b24e14 b24e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e132 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b24e32 X0 y
                 have i₂ := b24e51 (τ X0)
                 grind)
              | exact superpose b24e51 b24e32
              | exact resolve b24e32 b24e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32 b24e51
            have b24e140 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e132 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e132
              | exact resolve b24e132 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e132
            have b24e146 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
            clear b24e140
            have b24e150 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b24e146
                 have i₂ := b24e81 (σ y) (σ y)
                 grind)
              | exact superpose b24e81 b24e146
              | exact resolve b24e146 b24e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e81 b24e146
            have b24e151 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b24e150
            have b24e258 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b24e37 (σ y) (σ y) x
                 have i₂ := b24e151
                 grind)
              | exact superpose b24e151 b24e37
              | exact resolve b24e37 b24e151
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e37 b24e151
            have b24e267 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b24e28
                 have i₂ := b24e258 (σ x)
                 grind)
              | exact superpose b24e258 b24e28
              | (have r₁ := b24e28
                 have r₂ := b24e258 (σ x)
                 grind)
              | exact resolve b24e28 b24e258
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e258
            have b24e281 : False := by grind
            exact b24e281
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b25e23 : x ≠ (M.op y x) := by grind
              have b25e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e37 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
                intro X0
                first
                | (have i₁ := b25e15 y y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e45 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 (M.op x y) X1
                   have i₂ := b25e37 (M.op X0 (M.op x y))
                   grind)
                | exact superpose b25e37 b25e15
                | exact resolve b25e15 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e46 : ∀ X1 : G, x = (M.op X1 x) := by
                intro X1
                first
                | (have i₁ := b25e45 x X1
                   have i₂ := b25e37 x
                   grind)
                | exact superpose b25e37 b25e45
                | exact resolve b25e45 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37 b25e45
              have b25e72 : x ≠ x := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e46 y
                   grind)
                | exact superpose b25e46 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e46 y
                   grind)
                | exact resolve b25e23 b25e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e46
              have b25e79 : False := by grind
              exact b25e79
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : x ≠ (M.op y x) := by grind
              have b26e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 (τ X0) X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b26e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e33 X0 X1 x X3
                   have i₂ := b26e15 X0 X1 x
                   grind)
                | exact superpose b26e15 b26e33
                | exact resolve b26e33 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X0 X1 x
                   have i₂ := b26e35 (M.op X0 X1) X1 x
                   grind)
                | exact superpose b26e35 b26e15
                | exact resolve b26e15 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 (M.op X0 X1) X2
                   have i₂ := b26e35 X0 X1 X2
                   grind)
                | exact superpose b26e35 b26e18
                | (have j0 := b26e18 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e18 (M.op X0 X1) x
                   have r₂ := b26e35 X0 X1 x
                   grind)
                | exact resolve b26e18 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e44 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e42 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e42
              have b26e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e60 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e62 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 X0 X0 x
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e35 X0 X1 x
                   have i₂ := b26e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b26e20 b26e35
                | (have j1 := b26e20 X1 X0
                   grind)
                | exact resolve b26e35 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e60 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60
              have b26e88 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e30 X0 X1
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30
              have b26e102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e68 (σ X1) (σ X0)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e68
                | (have j0 := b26e68 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e68 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68
              have b26e186 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e88 (M.op X1 X2) X0
                   have i₂ := b26e44 X1 X2 (σ X0)
                   grind)
                | exact superpose b26e44 b26e88
                | exact resolve b26e88 b26e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44 b26e88
              have b26e190 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e186 X0 X1 X2
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e186
                | exact resolve b26e186 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e186
              have b26e209 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) (τ (M.op X0 X1))) := by
                intro X0 X1
                grind
              clear b26e190
              have b26e216 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e209 X0 X1
                   have i₂ := b26e40 (τ (M.op X0 X1)) (τ (M.op X0 X1))
                   grind)
                | exact superpose b26e40 b26e209
                | (have j0 := b26e209 X0 X1
                   grind)
                | exact resolve b26e209 b26e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e40 b26e209
              have b26e217 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have j0 := b26e216 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e216
              have b26e299 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (σ X1) (σ X1) x
                   have i₂ := b26e58 X0 X1
                   grind)
                | exact superpose b26e58 b26e35
                | (have j1 := b26e58 X0 X1
                   grind)
                | exact resolve b26e35 b26e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58
              have b26e905 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X0 X2
                   have i₂ := b26e62 X0 X3 (M.op X1 X0)
                   grind)
                | exact superpose b26e62 b26e15
                | (have j1 := b26e62 X0 X3 X2
                   grind)
                | exact resolve b26e15 b26e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e2064 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e102 y x
                   grind)
                | exact superpose b26e102 b26e22
                | (have j1 := b26e102 y x
                   grind)
                | exact resolve b26e22 b26e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e102
              have b26e2202 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e299 x X0 (σ y)
                   grind)
                | exact superpose b26e299 b26e25
                | (have j1 := b26e299 x X0 x
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e299 x x (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e299 y x x
                   grind)
                | exact resolve b26e25 b26e299
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e299
              have b26e2226 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2202 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2202
              have b26e13708 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b26e217 X0 X1
                   grind)
                | exact superpose b26e217 b26e35
                | exact resolve b26e35 b26e217
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e217
              have b26e16326 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2226 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2226
              have b26e16877 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e23
                   have i₂ := b26e905 x y X0 X1
                   grind)
                | (have i₁ := b26e23
                   have i₂ := b26e905 x X0 y X1
                   grind)
                | exact superpose b26e905 b26e23
                | (have j1 := b26e905 x X1 x X1
                   grind)
                | (have r₁ := b26e23
                   have r₂ := b26e905 y X1 x x
                   grind)
                | exact resolve b26e23 b26e905
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e905
              have b26e17040 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X1
                first
                | (have j0 := b26e16877 x X1
                   have j1 := b26e62 x X1 x
                   grind)
                | (have r₁ := b26e16877 x X1
                   have r₂ := b26e62 x X1 x
                   grind)
                | (have r₁ := b26e16877 x X1
                   have r₂ := b26e62 x x x
                   grind)
                | exact resolve b26e16877 b26e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e62 b26e16877
              have b26e27284 : ∀ X0 : G, (σ X0) ≠ (σ (M.op x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (M.op x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e16326 X0
                   have i₂ := b26e17040 X0
                   grind)
                | exact superpose b26e17040 b26e16326
                | (have j0 := b26e16326 X0
                   have j1 := b26e17040 X0
                   grind)
                | exact resolve b26e16326 b26e17040
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e16326
              have b26e70725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e2064
                   have i₂ := b26e17040 y
                   grind)
                | exact superpose b26e17040 b26e2064
                | (have j1 := b26e17040 y
                   grind)
                | exact resolve b26e2064 b26e17040
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2064 b26e17040
              have b26e70753 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
              clear b26e70725
              have b26e70769 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have j1 := b26e27284 y
                   grind)
                | (have r₁ := b26e70753
                   have r₂ := b26e27284 y
                   grind)
                | exact resolve b26e70753 b26e27284
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e27284 b26e70753
              have b26e70781 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e70769
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e70769 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70769
              have b26e70826 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
                intro X0
                first
                | (have i₁ := b26e13708 (σ x) (σ y) x
                   have i₂ := b26e70781
                   grind)
                | exact superpose b26e70781 b26e13708
                | exact resolve b26e13708 b26e70781
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e13708 b26e70781
              have b26e70836 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e70826 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e70826
                | exact resolve b26e70826 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70826
              have b26e70890 : y ≠ y := by
                first
                | (have i₁ := b26e27
                   have i₂ := b26e70836 x
                   grind)
                | exact superpose b26e70836 b26e27
                | (have r₁ := b26e27
                   have r₂ := b26e70836 x
                   grind)
                | exact resolve b26e27 b26e70836
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70836
              have b26e70932 : False := by grind
              exact b26e70932

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_y_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e11 y x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e33
        | exact resolve b0e33 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e40 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e59 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e39 (σ x)
           grind)
        | exact superpose b0e39 b0e18
        | exact resolve b0e18 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e60 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e59
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e59
        | exact resolve b0e59 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e59
      have b0e61 : False := by grind
      exact b0e61
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b1e24 : y ≠ y ∨ x = (k x y) := by
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
        have b1e27 : x = (k x y) := by grind
        clear b1e24
        have b1e31 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b1e12 y x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e31 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e31
          | exact resolve b1e31 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e43 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e39 x
             grind)
          | exact superpose b1e39 b1e23
          | exact resolve b1e23 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e39
        have b1e47 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e52 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e21
             grind)
          | exact resolve b1e50 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e54 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e54
          | exact resolve b1e54 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e54
        have b1e56 : False := by grind
        exact b1e56
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : y ≠ y ∨ x = (k x y) := by
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
        have b2e24 : x = (k x y) := by grind
        clear b2e23
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b2e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e29 X0 X1 x X3
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e31 (M.op X0 X1) X1 x
             grind)
          | exact superpose b2e31 b2e12
          | exact resolve b2e12 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 (M.op X0 X1)
             have i₂ := b2e58 X0 X1
             grind)
          | exact superpose b2e58 b2e15
          | (have j0 := b2e15 X1 (M.op X0 X1)
             grind)
          | (have r₁ := b2e15 X1 (M.op X0 X1)
             have r₂ := b2e58 X0 X1
             grind)
          | exact resolve b2e15 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e90 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e86 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e157 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e47 y x
             grind)
          | exact superpose b2e47 b2e22
          | (have j1 := b2e47 y x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e47 y x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e47 x y
             grind)
          | exact resolve b2e22 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e171 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b2e157
        have b2e178 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e171
             have r₂ := b2e21
             grind)
          | exact resolve b2e171 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171
        have b2e187 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e178
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e178
          | exact resolve b2e178 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e178
        have b2e211 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e187
             grind)
          | exact superpose b2e187 b2e21
          | exact resolve b2e21 b2e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e219 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e90 (σ y) (σ x)
             have i₂ := b2e187
             grind)
          | exact superpose b2e187 b2e90
          | exact resolve b2e90 b2e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90 b2e187
        have b2e220 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e219
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e219
          | exact resolve b2e219 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e219
        have b2e286 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e220
             grind)
          | exact superpose b2e220 b2e13
          | exact resolve b2e13 b2e220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e220
        have b2e304 : x = (k x x) := by
          first
          | (have i₁ := b2e286
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e286
          | exact resolve b2e286 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e286
        have b2e320 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e304
             grind)
          | exact superpose b2e304 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e304
        have b2e321 : x = (M.op x x) := by grind
        clear b2e320
        have b2e347 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e31 x x x
             have i₂ := b2e321
             grind)
          | exact superpose b2e321 b2e31
          | exact resolve b2e31 b2e321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e321
        have b2e401 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e347 y
             grind)
          | exact superpose b2e347 b2e20
          | exact resolve b2e20 b2e347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e347
        have b2e453 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e211
             have i₂ := b2e401
             grind)
          | exact superpose b2e401 b2e211
          | exact resolve b2e211 b2e401
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e211 b2e401
        have b2e459 : False := by grind
        exact b2e459
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b3e24 : x ≠ x ∨ y = (k y x) := by
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
        have b3e27 : y = (k y x) := by grind
        clear b3e24
        have b3e32 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e32 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e32
          | exact resolve b3e32 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e47 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
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
        have b3e50 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b3e47
        have b3e52 : (σ x) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e23
             grind)
          | exact resolve b3e50 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e54 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e54
          | exact resolve b3e54 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e54
        have b3e64 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e23
          | exact resolve b3e23 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e55
        have b3e72 : False := by grind
        exact b3e72
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : x ≠ x ∨ y = (k y x) := by
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
          have b5e27 : y = (k y x) := by grind
          clear b5e26
          have b5e30 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b5e13 x y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b5e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e32 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e32
            | exact resolve b5e32 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e36 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e30
            | exact resolve b5e30 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e40 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e36 y
               grind)
            | exact superpose b5e36 b5e21
            | exact resolve b5e21 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e34 (M.op X0 X1) X1 x
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e99 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 (M.op X0 X1)
               have i₂ := b5e61 X0 X1
               grind)
            | exact superpose b5e61 b5e16
            | (have j0 := b5e16 X1 (M.op X0 X1)
               grind)
            | (have r₁ := b5e16 X1 (M.op X0 X1)
               have r₂ := b5e61 X0 X1
               grind)
            | exact resolve b5e16 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e103 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e99 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e148 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e50 x y
               grind)
            | exact superpose b5e50 b5e23
            | (have j1 := b5e50 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e50 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e50 y x
               grind)
            | exact resolve b5e23 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e162 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e148
          have b5e169 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e162
               have r₂ := b5e24
               grind)
            | exact resolve b5e162 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e162
          have b5e176 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e169
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e169
            | exact resolve b5e169 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e169
          have b5e184 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b5e103 (σ x) (σ y)
               have i₂ := b5e176
               grind)
            | exact superpose b5e176 b5e103
            | exact resolve b5e103 b5e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103 b5e176
          have b5e185 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e184
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e184
            | exact resolve b5e184 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184
          have b5e258 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e185
               grind)
            | exact superpose b5e185 b5e14
            | exact resolve b5e14 b5e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185
          have b5e276 : y = (k y y) := by
            first
            | (have i₁ := b5e258
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e258
            | exact resolve b5e258 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e258
          have b5e299 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e276
               grind)
            | exact superpose b5e276 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e276
          have b5e300 : y = (M.op y y) := by grind
          clear b5e299
          have b5e306 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e34 y y x
               have i₂ := b5e300
               grind)
            | exact superpose b5e300 b5e34
            | exact resolve b5e34 b5e300
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e300
          have b5e341 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e306 x
               grind)
            | exact superpose b5e306 b5e22
            | exact resolve b5e22 b5e306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e306
          have b5e342 : False := by grind
          exact b5e342
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e23
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
        have b6e38 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e38 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e38
          | exact resolve b6e38 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e51 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
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
        have b6e54 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b6e51
        have b6e55 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e44 (σ x)
             grind)
          | exact superpose b6e44 b6e54
          | exact resolve b6e54 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e54
        have b6e56 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e55
          | exact resolve b6e55 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e61 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
        have b6e64 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e61
             have r₂ := b6e21
             grind)
          | exact resolve b6e61 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e67 : x = (M.op y x) := by
          first
          | (have r₁ := b6e64
             have r₂ := b6e20
             grind)
          | exact resolve b6e64 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e69 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e67
             grind)
          | exact superpose b6e67 b6e20
          | exact resolve b6e20 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e105 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e13
          | exact resolve b6e13 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e106 : x = (k y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e105
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e105
          | exact resolve b6e105 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e349 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e106
             grind)
          | exact superpose b6e106 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e350 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
        clear b6e349
        have b6e352 : y = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e350
             have r₂ := b6e21
             grind)
          | exact resolve b6e350 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e350
        have b6e354 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e352
             have r₂ := b6e20
             grind)
          | exact resolve b6e352 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e352
        have b6e358 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e354
             grind)
          | exact superpose b6e354 b6e13
          | exact resolve b6e13 b6e354
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e354
        have b6e375 : x = y := by
          first
          | (have i₁ := b6e358
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e358
          | exact resolve b6e358 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e358
        have b6e379 : False := by grind
        exact b6e379
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e50 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e53 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e50
          have b7e54 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e53
               have r₂ := b7e23
               grind)
            | exact resolve b7e53 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e55 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e54
            | exact resolve b7e54 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e77 : (τ (σ y)) = (k x y) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e14
            | exact resolve b7e14 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e78 : y = (k x y) := by
            first
            | (have i₁ := b7e77
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e77
            | exact resolve b7e77 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e97 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e98 : y = (M.op y x) ∨ x = (M.op x y) := by grind
          clear b7e97
          have b7e100 : x = (M.op x y) := by
            first
            | (have r₁ := b7e98
               have r₂ := b7e21
               grind)
            | exact resolve b7e98 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e102 : False := by grind
          exact b7e102
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e61 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e157 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e61 x y
               grind)
            | exact superpose b8e61 b8e23
            | (have j1 := b8e61 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e61 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e61 y x
               grind)
            | exact resolve b8e23 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e171 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e157
          have b8e178 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e171
               have r₂ := b8e24
               grind)
            | exact resolve b8e171 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171
          have b8e202 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e178
               grind)
            | exact superpose b8e178 b8e20
            | exact resolve b8e20 b8e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e202
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e202
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e202 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e202
          have b8e276 : y = (M.op y x) ∨ x = (M.op x y) := by grind
          clear b8e275
          have b8e277 : x = (M.op x y) := by
            first
            | (have r₁ := b8e276
               have r₂ := b8e21
               grind)
            | exact resolve b8e276 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276
          have b8e278 : False := by grind
          exact b8e278
