import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
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
        have b1e49 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e51 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e49
        have b1e52 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e51
             have r₂ := b1e23
             grind)
          | exact resolve b1e51 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e53 : (σ y) = (σ (k x y)) := by
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
        have b1e54 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e53
          | exact resolve b1e53 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e53
        have b1e55 : False := by grind
        exact b1e55
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
        have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e734 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e139 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e139
          | (have j0 := b2e139 x y
             grind)
          | exact resolve b2e139 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e139
        have b2e737 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e734
        have b2e753 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e737
             have r₂ := b2e22
             grind)
          | exact resolve b2e737 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e737
        have b2e760 : False := by grind
        exact b2e760
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
        have b3e47 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e49 : x = y ∨ y = (k x y) := by grind
        clear b3e47
        have b3e50 : y = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e23
             grind)
          | exact resolve b3e49 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e49
        have b3e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e29
          | exact resolve b3e29 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e50
        have b3e54 : False := by grind
        exact b3e54
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
          have b5e51 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e55 : x = y ∨ y = (k x y) := by grind
          clear b5e51
          have b5e56 : y = (k x y) := by
            first
            | (have r₁ := b5e55
               have r₂ := b5e25
               grind)
            | exact resolve b5e55 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e55
          have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e166 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e1004 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e166 x y
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e166
            | (have j0 := b5e166 x y
               grind)
            | exact resolve b5e166 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e166
          have b5e1007 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e1004
          have b5e1010 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1007
               have r₂ := b5e24
               grind)
            | exact resolve b5e1007 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1007
          have b5e1020 : False := by grind
          exact b5e1020
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
        have b6e53 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e55 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e53
        have b6e58 : y = (M.op x y) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e21
             grind)
          | exact resolve b6e55 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e61 : False := by grind
        exact b6e61
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
          have b7e45 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e25
               grind)
            | exact resolve b7e47 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e47
          have b7e49 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : y = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e62 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e63 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e62
          have b7e65 : x = (M.op x y) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : False := by grind
          exact b7e67
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
          have b8e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e99 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e45 x y
               grind)
            | exact superpose b8e45 b8e20
            | (have j1 := b8e45 x y
               grind)
            | exact resolve b8e20 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45
          have b8e116 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e99
               have r₂ := b8e24
               grind)
            | exact resolve b8e99 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e119 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e116
               have r₂ := b8e23
               grind)
            | exact resolve b8e116 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e120 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e119
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e119
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e119 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e121 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e120
          have b8e122 : y = (M.op x y) := by
            first
            | (have r₁ := b8e121
               have r₂ := b8e22
               grind)
            | exact resolve b8e121 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e123 : False := by grind
          exact b8e123

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

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e41 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) x
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e42 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e46 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e41 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e56 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e45 (σ X0)
           grind)
        | exact superpose b0e45 b0e17
        | exact resolve b0e17 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e57 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e56 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e56
        | exact resolve b0e56 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e56
      have b0e174 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e57 y
           grind)
        | exact superpose b0e57 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e57 y
           grind)
        | exact resolve b0e18 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e183 : False := by grind
      exact b0e183
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e70 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X2 X0
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X1
             have j1 := b1e17 X2 X2
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 X0 X1
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e80 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e70 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e1067 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e80 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e1068 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e1067 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1067
        have b1e1079 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e1068 X0
             have j1 := b1e15 X0 X0
             grind)
          | (have r₁ := b1e1068 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e1068 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1068
        have b1e1107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e1079 (σ X0)
             grind)
          | exact superpose b1e1079 b1e18
          | exact resolve b1e18 b1e1079
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1116 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e1107 X0
             have i₂ := b1e1079 X0
             grind)
          | exact superpose b1e1079 b1e1107
          | exact resolve b1e1107 b1e1079
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1079 b1e1107
        have b1e2754 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1116 x
             grind)
          | exact superpose b1e1116 b1e21
          | exact resolve b1e21 b1e1116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1116
        have b1e2805 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2754
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2754
          | exact resolve b1e2754 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2754
        have b1e2806 : False := by grind
        exact b1e2806
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X2 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e79 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e67 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e892 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e79 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e893 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e892 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e892
        have b2e901 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e893 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e893 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e893 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e893
        have b2e923 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e901 (σ X0)
             grind)
          | exact superpose b2e901 b2e18
          | exact resolve b2e18 b2e901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e930 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e923 X0
             have i₂ := b2e901 X0
             grind)
          | exact superpose b2e901 b2e923
          | exact resolve b2e923 b2e901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e901 b2e923
        have b2e1530 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e930 x
             grind)
          | exact superpose b2e930 b2e21
          | exact resolve b2e21 b2e930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e930
        have b2e1567 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1530
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1530
          | exact resolve b2e1530 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1530
        have b2e1568 : False := by grind
        exact b2e1568
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e40 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b3e43 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e54 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e43 (σ X0)
             grind)
          | exact superpose b3e43 b3e18
          | exact resolve b3e18 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e158 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e54 x
             grind)
          | exact superpose b3e54 b3e22
          | exact resolve b3e22 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e209 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e158
             grind)
          | exact superpose b3e158 b3e13
          | exact resolve b3e13 b3e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e158
        have b3e211 : x = (k x x) := by
          first
          | (have i₁ := b3e209
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e209
          | exact resolve b3e209 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209
        have b3e350 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e211
             grind)
          | exact superpose b3e211 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e211
        have b3e351 : x = (M.op x x) := by grind
        clear b3e350
        have b3e353 : False := by grind
        exact b3e353
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e14
            | exact resolve b4e14 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
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
          have b4e32 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
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
          have b4e33 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ y) X0)) := by
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
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X2 X2
               have i₂ := b4e13 X2 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op (M.op X2 X3) X0) X3
               have i₂ := b4e13 X0 X3 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 X1) X1 X2
               have i₂ := b4e13 (M.op X2 X1) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b4e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e16 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) X0
               grind)
            | (have r₁ := b4e16 (σ y) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e50 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e78 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e78 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e106 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e26 X1 X0
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e148 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e32 X0
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e32
            | exact resolve b4e32 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e162 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30
            | exact resolve b4e30 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e253 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e106 y X0
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e106
            | exact resolve b4e106 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e106
          have b4e268 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e253 X0
               have i₂ := b4e50 (τ X0)
               grind)
            | exact superpose b4e50 b4e253
            | exact resolve b4e253 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50 b4e253
          have b4e357 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X3 (M.op (M.op X4 X3) (M.op (M.op X5 (M.op X6 X7)) X2))) = (M.op X7 (M.op X0 (M.op (M.op X1 X0) X2))) := by
            intro X0 X1 X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b4e31 X3 X4 (M.op (M.op X5 (M.op X6 X7)) X2) X7 X6
               have i₂ := b4e31 (M.op X6 X7) X5 X2 X0 X1
               grind)
            | (have i₁ := b4e31 X3 X4 (M.op (M.op X5 (M.op X6 X7)) X2) X7 X6
               have i₂ := b4e31 X0 X1 X2 (M.op X6 X7) X5
               grind)
            | exact superpose b4e31 b4e31
            | exact resolve b4e31 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e373 : ∀ X2 X3 X4 X5 X6 X7 : G, (M.op X3 (M.op (M.op X4 X3) (M.op (M.op X5 (M.op X6 X7)) X2))) = (M.op X7 (M.op y (M.op y X2))) := by
            intro X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b4e357 x x X2 X3 X4 X5 X6 X7
               have i₂ := b4e41 X2 x x
               grind)
            | exact superpose b4e41 b4e357
            | exact resolve b4e357 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e357
          have b4e430 : ∀ X2 X5 X6 X7 : G, (M.op X7 (M.op y (M.op y X2))) = (M.op y (M.op y (M.op (M.op X5 (M.op X6 X7)) X2))) := by
            intro X2 X5 X6 X7
            first
            | (have i₁ := b4e373 X2 x x X5 X6 X7
               have i₂ := b4e41 (M.op (M.op X5 (M.op X6 X7)) X2) x x
               grind)
            | exact superpose b4e41 b4e373
            | exact resolve b4e373 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e373
          have b4e539 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X0 X0)) = (M.op X5 (M.op (M.op X6 X5) (M.op (M.op X3 (M.op (M.op X4 X3) (M.op X2 X1))) X0))) := by
            intro X0 X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b4e31 X1 X2 (M.op (M.op X3 (M.op (M.op X4 X3) (M.op X2 X1))) X0) X5 X6
               have i₂ := b4e34 X3 X4 (M.op X2 X1) X0
               grind)
            | exact superpose b4e34 b4e31
            | exact resolve b4e31 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e542 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X0)) = (M.op y (M.op y (M.op (M.op X3 (M.op (M.op X4 X3) (M.op X2 X1))) X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e539 X0 X1 X2 X3 X4 x x
               have i₂ := b4e41 (M.op (M.op X3 (M.op (M.op X4 X3) (M.op X2 X1))) X0) x x
               grind)
            | exact superpose b4e41 b4e539
            | exact resolve b4e539 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e539
          have b4e606 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X2 X1) (M.op y (M.op y X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e542 X0 X1 X2 x x
               have i₂ := b4e430 X0 x (M.op x x) (M.op X2 X1)
               grind)
            | exact superpose b4e430 b4e542
            | exact resolve b4e542 b4e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e542
          have b4e744 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0)) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) (M.op X0 X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e35 (M.op X1 X2) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0) X3 X4
               have i₂ := b4e35 (M.op X1 X2) X0 X1 X2
               grind)
            | exact superpose b4e35 b4e35
            | exact resolve b4e35 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e758 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) = (M.op (M.op (M.op X3 X4) X2) (M.op X0 X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e35 X2 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4
               have i₂ := b4e13 X0 (M.op X2 X2) X1
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e801 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b4e32 (M.op (M.op X0 X0) X0)
               have i₂ := b4e35 X0 X0 X0 X0
               grind)
            | exact superpose b4e35 b4e32
            | exact resolve b4e32 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e846 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X2) (M.op X0 X0)) = (M.op (σ y) (M.op (σ y) (M.op (M.op X1 (M.op X2 X2)) X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e758 X0 X1 X2 X3 X4
               have i₂ := b4e33 (M.op (M.op X1 (M.op X2 X2)) X0)
               grind)
            | exact superpose b4e33 b4e758
            | exact resolve b4e758 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e758
          have b4e854 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X1 X2)) (M.op X0 X0)) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e744 X0 X1 X2 X3 X4
               have i₂ := b4e33 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0)
               grind)
            | exact superpose b4e33 b4e744
            | exact resolve b4e744 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e744
          have b4e892 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X2) (M.op X0 X0)) = (M.op y (M.op y (M.op (M.op X1 (M.op X2 X2)) X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e846 X0 X1 X2 X3 X4
               have i₂ := b4e148 (M.op (M.op X1 (M.op X2 X2)) X0)
               grind)
            | exact superpose b4e148 b4e846
            | exact resolve b4e846 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e846
          have b4e899 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X1 X2)) (M.op X0 X0)) = (M.op y (M.op y (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e854 X0 X1 X2 X3 X4
               have i₂ := b4e148 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0)
               grind)
            | exact superpose b4e148 b4e854
            | exact resolve b4e854 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e854
          have b4e909 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X2) (M.op X0 X0)) = (M.op X2 (M.op y (M.op y X0))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b4e892 X0 x X2 X3 X4
               have i₂ := b4e430 X0 x X2 X2
               grind)
            | exact superpose b4e430 b4e892
            | exact resolve b4e892 b4e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e892
          have b4e913 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X1 X2)) (M.op X0 X0)) = (M.op X2 (M.op y (M.op y X0))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e899 X0 X1 X2 X3 X4
               have i₂ := b4e430 X0 (M.op X1 X2) X1 X2
               grind)
            | exact superpose b4e430 b4e899
            | exact resolve b4e899 b4e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e899
          have b4e920 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op y X0))) = (M.op (M.op X1 X2) (M.op y (M.op y X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e913 X0 X1 X2 x x
               have i₂ := b4e909 X0 (M.op X1 X2) x x
               grind)
            | exact superpose b4e909 b4e913
            | exact resolve b4e913 b4e909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e909 b4e913
          have b4e1008 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e89 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e1009 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e1008 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1008
          have b4e1018 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1009 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e1009 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e1009 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1009
          have b4e1045 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e1018 (σ X0)
               grind)
            | exact superpose b4e1018 b4e19
            | exact resolve b4e19 b4e1018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1047 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e162 X0 X0
               have i₂ := b4e1018 (τ X0)
               grind)
            | exact superpose b4e1018 b4e162
            | exact resolve b4e162 b4e1018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e162
          have b4e1054 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1047 X0
               have i₂ := b4e1018 X0
               grind)
            | exact superpose b4e1018 b4e1047
            | exact resolve b4e1047 b4e1018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1047
          have b4e1056 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1045 X0
               have i₂ := b4e1018 X0
               grind)
            | exact superpose b4e1018 b4e1045
            | exact resolve b4e1045 b4e1018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1018 b4e1045
          have b4e1176 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op y (τ (M.op (σ y) X0))) := by
            intro X0
            first
            | (have i₁ := b4e268 (M.op (σ y) X0)
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e268
            | exact resolve b4e268 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1201 : ∀ X0 : G, (M.op y (M.op y (τ X0))) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1176 X0
               have i₂ := b4e268 X0
               grind)
            | exact superpose b4e268 b4e1176
            | exact resolve b4e1176 b4e268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e268 b4e1176
          have b4e1256 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) x
               have i₂ := b4e34 X0 X1 (M.op X1 X0) x
               grind)
            | exact superpose b4e34 b4e36
            | exact resolve b4e36 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e36
          have b4e1427 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op y (M.op y (σ X0))) := by
            intro X0
            first
            | (have i₁ := b4e32 (σ X0)
               have i₂ := b4e1056 X0
               grind)
            | exact superpose b4e1056 b4e32
            | exact resolve b4e32 b4e1056
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1499 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2)) = (M.op (M.op y X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 X0 X1 y (M.op y X0)
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e37
            | exact resolve b4e37 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1644 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X2 X2)) = (M.op (σ y) (M.op (σ y) (M.op (M.op X1 (M.op X0 X0)) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1499 X0 X1 X2
               have i₂ := b4e33 (M.op (M.op X1 (M.op X0 X0)) X2)
               grind)
            | exact superpose b4e33 b4e1499
            | exact resolve b4e1499 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1499
          have b4e1714 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X2 X2)) = (M.op y (M.op y (M.op (M.op X1 (M.op X0 X0)) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1644 X0 X1 X2
               have i₂ := b4e148 (M.op (M.op X1 (M.op X0 X0)) X2)
               grind)
            | exact superpose b4e148 b4e1644
            | exact resolve b4e1644 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1644
          have b4e1758 : ∀ X0 X2 : G, (M.op (M.op y X0) (M.op X2 X2)) = (M.op X0 (M.op y (M.op y X2))) := by
            intro X0 X2
            first
            | (have i₁ := b4e1714 X0 x X2
               have i₂ := b4e430 X2 x X0 X0
               grind)
            | exact superpose b4e430 b4e1714
            | exact resolve b4e1714 b4e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1714
          have b4e2466 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op y (M.op y (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op X0 X0)
               have i₂ := b4e1201 X0
               grind)
            | exact superpose b4e1201 b4e15
            | exact resolve b4e15 b4e1201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1201
          have b4e2750 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op y (M.op y (σ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1427 X0
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e1427
            | exact resolve b4e1427 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e2783 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 X0 y y (σ X0)
               have i₂ := b4e1427 X0
               grind)
            | exact superpose b4e1427 b4e37
            | exact resolve b4e37 b4e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1427
          have b4e2798 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op X0 X0)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2783 X0 X1
               have i₂ := b4e33 (M.op (σ (M.op X0 X0)) X1)
               grind)
            | exact superpose b4e33 b4e2783
            | exact resolve b4e2783 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2783
          have b4e2810 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op y (M.op y (M.op (σ (M.op X0 X0)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2798 X0 X1
               have i₂ := b4e148 (M.op (σ (M.op X0 X0)) X1)
               grind)
            | exact superpose b4e148 b4e2798
            | exact resolve b4e2798 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2798
          have b4e3142 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op (M.op (M.op X1 (σ (M.op y (M.op y (τ X0))))) X2) (M.op (M.op X1 (σ (M.op y (M.op y (τ X0))))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 X0 X1 X0 X0
               have i₂ := b4e2466 X0
               grind)
            | exact superpose b4e2466 b4e37
            | exact resolve b4e37 b4e2466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2466
          have b4e3184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op (σ y) (M.op (σ y) (M.op (M.op X1 (σ (M.op y (M.op y (τ X0))))) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3142 X0 X1 X2
               have i₂ := b4e33 (M.op (M.op X1 (σ (M.op y (M.op y (τ X0))))) X2)
               grind)
            | exact superpose b4e33 b4e3142
            | exact resolve b4e3142 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3142
          have b4e3264 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op y (M.op y (M.op (M.op X1 (σ (M.op y (M.op y (τ X0))))) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3184 X0 X1 X2
               have i₂ := b4e148 (M.op (M.op X1 (σ (M.op y (M.op y (τ X0))))) X2)
               grind)
            | exact superpose b4e148 b4e3184
            | exact resolve b4e3184 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3184
          have b4e3332 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op y (M.op y (M.op (M.op X1 (M.op y (M.op y (σ (τ X0))))) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3264 X0 X1 X2
               have i₂ := b4e2750 (τ X0)
               grind)
            | exact superpose b4e2750 b4e3264
            | exact resolve b4e3264 b4e2750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2750 b4e3264
          have b4e3344 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op (M.op y (σ (τ X0))) (M.op y (M.op y X2))) := by
            intro X0 X2
            first
            | (have i₁ := b4e3332 X0 x X2
               have i₂ := b4e430 X2 x y (M.op y (σ (τ X0)))
               grind)
            | exact superpose b4e430 b4e3332
            | exact resolve b4e3332 b4e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e430 b4e3332
          have b4e3347 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op (σ (τ X0)) (M.op y (M.op y X2))) := by
            intro X0 X2
            first
            | (have i₁ := b4e3344 X0 X2
               have i₂ := b4e920 X2 y (σ (τ X0))
               grind)
            | exact superpose b4e920 b4e3344
            | exact resolve b4e3344 b4e920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344
          have b4e3348 : ∀ X0 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op y (M.op y X2))) := by
            intro X0 X2
            first
            | (have i₁ := b4e3347 X0 X2
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e3347
            | exact resolve b4e3347 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3347
          have b4e7004 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op y (M.op y (M.op (σ (M.op X0 X0)) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e801 (σ X0)
               have i₂ := b4e1056 X0
               grind)
            | exact superpose b4e1056 b4e801
            | exact resolve b4e801 b4e1056
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e801
          have b4e7058 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b4e7004 X0
               have i₂ := b4e2810 X0 (σ X0)
               grind)
            | exact superpose b4e2810 b4e7004
            | exact resolve b4e7004 b4e2810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2810 b4e7004
          have b4e7088 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e7058 X0
               have i₂ := b4e1056 X0
               grind)
            | exact superpose b4e1056 b4e7058
            | exact resolve b4e7058 b4e1056
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1056 b4e7058
          have b4e7177 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e1256 (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1256
            | exact resolve b4e1256 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7280 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ y) (σ y)))) = (M.op y (M.op y (M.op X0 (M.op (σ y) (σ y))))) := by
            intro X0
            first
            | (have i₁ := b4e148 (M.op X0 (M.op (σ y) (σ y)))
               have i₂ := b4e1256 (σ y) X0
               grind)
            | exact superpose b4e1256 b4e148
            | exact resolve b4e148 b4e1256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1256
          have b4e7295 : ∀ X0 : G, (M.op y (M.op y (M.op X0 (σ y)))) = (M.op (σ y) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e7280 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e7280
            | exact resolve b4e7280 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7280
          have b4e7350 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (M.op y (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b4e7295 X0
               have i₂ := b4e7177 X0
               grind)
            | exact superpose b4e7177 b4e7295
            | exact resolve b4e7295 b4e7177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7177 b4e7295
          have b4e12813 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (M.op (σ (τ X0)) (σ (τ (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e7088 (τ X0)
               have i₂ := b4e1054 X0
               grind)
            | exact superpose b4e1054 b4e7088
            | exact resolve b4e7088 b4e1054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7088
          have b4e12860 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (τ X0)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e12813 X0
               have i₂ := b4e15 (M.op X0 X0)
               grind)
            | exact superpose b4e15 b4e12813
            | exact resolve b4e12813 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12813
          have b4e12914 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e12860 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e12860
            | exact resolve b4e12860 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12860
          have b4e13725 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y y)) = (M.op X0 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e606 y X0 X1
               have i₂ := b4e12914 y
               grind)
            | exact superpose b4e12914 b4e606
            | exact resolve b4e606 b4e12914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e13785 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 (M.op X1 X1)) (M.op y (M.op y X1))) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 (M.op X1 X1) X2
               have i₂ := b4e606 X1 (M.op X1 X1) X0
               grind)
            | exact superpose b4e606 b4e16
            | (have j0 := b4e16 (M.op X1 X1) X2
               grind)
            | exact resolve b4e16 b4e606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e14167 : ∀ X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X1 X1) (M.op y (M.op y X1))) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b4e13785 x X1 X2
               have i₂ := b4e920 X1 x (M.op X1 X1)
               grind)
            | exact superpose b4e920 b4e13785
            | (have j0 := b4e13785 x X1 X2
               grind)
            | exact resolve b4e13785 b4e920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e920 b4e13785
          have b4e14226 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13725 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13725
            | exact resolve b4e13725 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13725
          have b4e14548 : ∀ X1 X2 : G, (M.op X1 X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b4e14167 X1 X2
               have i₂ := b4e606 X1 X1 X1
               grind)
            | exact superpose b4e606 b4e14167
            | (have j0 := b4e14167 X1 X2
               grind)
            | exact resolve b4e14167 b4e606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e606 b4e14167
          have b4e14742 : ∀ X1 X2 : G, (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) := by
            intro X1 X2
            first
            | (have j0 := b4e14548 X1 X2
               grind)
            | (have r₁ := b4e14548 x X2
               have r₂ := b4e12914 x
               grind)
            | exact resolve b4e14548 b4e12914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12914 b4e14548
          have b4e14934 : ∀ X0 : G, (M.op (τ X0) y) = (M.op (τ (M.op X0 X0)) y) := by
            intro X0
            first
            | (have i₁ := b4e14226 (τ X0) (τ X0)
               have i₂ := b4e1054 X0
               grind)
            | exact superpose b4e1054 b4e14226
            | exact resolve b4e14226 b4e1054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14226
          have b4e16877 : ∀ X0 : G, (M.op X0 (M.op y (M.op y (σ y)))) = (M.op (M.op y X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1758 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1758
            | exact resolve b4e1758 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1758
          have b4e17100 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op y X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e16877 X0
               have i₂ := b4e3348 X0 (σ y)
               grind)
            | exact superpose b4e3348 b4e16877
            | exact resolve b4e16877 b4e3348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3348 b4e16877
          have b4e17165 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op y X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17100 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17100
            | exact resolve b4e17100 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17100
          have b4e17255 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (k (τ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e14742 (τ X0) x
               have i₂ := b4e1054 X0
               grind)
            | exact superpose b4e1054 b4e14742
            | exact resolve b4e14742 b4e1054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1054
          have b4e17286 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (τ (M.op (M.op X0 X0) (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (M.op X0 X0) X1
               have i₂ := b4e14742 X0 (σ X1)
               grind)
            | exact superpose b4e14742 b4e30
            | exact resolve b4e30 b4e14742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e14742
          have b4e18202 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (σ y))) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op (M.op X0 X1) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 (σ y) y x x
               have i₂ := b4e17165 (M.op x x)
               grind)
            | exact superpose b4e17165 b4e37
            | exact resolve b4e37 b4e17165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e17165
          have b4e18233 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ y) (M.op (M.op X0 X1) (σ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e18202 X0 X1
               have i₂ := b4e33 (M.op (M.op X0 X1) (σ y))
               grind)
            | exact superpose b4e33 b4e18202
            | exact resolve b4e18202 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e18202
          have b4e18261 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (σ y))) = (M.op y (M.op y (M.op (M.op X0 X1) (σ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e18233 X0 X1
               have i₂ := b4e148 (M.op (M.op X0 X1) (σ y))
               grind)
            | exact superpose b4e148 b4e18233
            | exact resolve b4e18233 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148 b4e18233
          have b4e18278 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X1 (M.op (σ y) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e18261 X0 X1
               have i₂ := b4e7350 (M.op X0 X1)
               grind)
            | exact superpose b4e7350 b4e18261
            | exact resolve b4e18261 b4e7350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7350 b4e18261
          have b4e18284 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e18278 X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e18278
            | exact resolve b4e18278 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18278
          have b4e548557 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k (τ (M.op X0 X0)) y) := by
            intro X0
            first
            | (have i₁ := b4e17286 X0 y
               have i₂ := b4e18284 X0 X0
               grind)
            | exact superpose b4e18284 b4e17286
            | exact resolve b4e17286 b4e18284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17286 b4e18284
          have b4e548594 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op (τ (M.op X0 X0)) y) := by
            intro X0
            first
            | (have i₁ := b4e548557 X0
               have i₂ := b4e17255 X0 y
               grind)
            | exact superpose b4e17255 b4e548557
            | exact resolve b4e548557 b4e17255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17255 b4e548557
          have b4e548620 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e548594 X0
               have i₂ := b4e14934 X0
               grind)
            | exact superpose b4e14934 b4e548594
            | exact resolve b4e548594 b4e14934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14934 b4e548594
          have b4e554552 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op X0 (σ y))
               have i₂ := b4e548620 X0
               grind)
            | exact superpose b4e548620 b4e15
            | exact resolve b4e15 b4e548620
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e548620
          have b4e560052 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e554552 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e554552
            | exact resolve b4e554552 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e554552
          have b4e566266 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e560052 x
               grind)
            | exact superpose b4e560052 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e560052 x
               grind)
            | exact resolve b4e20 b4e560052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e560052
          have b4e566433 : False := by grind
          exact b4e566433
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e78 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X2 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e78 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e876 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e91 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e877 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e876 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e876
          have b5e885 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e877 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e877 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e877 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e877
          have b5e907 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e885 (σ X0)
               grind)
            | exact superpose b5e885 b5e19
            | exact resolve b5e19 b5e885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e914 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e907 X0
               have i₂ := b5e885 X0
               grind)
            | exact superpose b5e885 b5e907
            | exact resolve b5e907 b5e885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e885 b5e907
          have b5e1764 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e914 y
               grind)
            | exact superpose b5e914 b5e24
            | exact resolve b5e24 b5e914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e914
          have b5e1803 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1764
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1764
            | exact resolve b5e1764 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1764
          have b5e1804 : False := by grind
          exact b5e1804
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e35 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e39 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e37 (σ X0)
             grind)
          | exact superpose b6e37 b6e18
          | exact resolve b6e18 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e108 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e39 x
             grind)
          | exact superpose b6e39 b6e22
          | exact resolve b6e22 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e151 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e108
             grind)
          | exact superpose b6e108 b6e13
          | exact resolve b6e13 b6e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108
        have b6e153 : x = (k x x) := by
          first
          | (have i₁ := b6e151
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e151
          | exact resolve b6e151 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e151
        have b6e211 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e212 : x = (M.op x x) := by grind
        clear b6e211
        have b6e214 : False := by grind
        exact b6e214
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e45 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e47 (σ X0)
               grind)
            | exact superpose b7e47 b7e19
            | exact resolve b7e19 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e128 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e49 y
               grind)
            | exact superpose b7e49 b7e24
            | exact resolve b7e24 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e174 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e128
               grind)
            | exact superpose b7e128 b7e14
            | exact resolve b7e14 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e176 : y = (k y y) := by
            first
            | (have i₁ := b7e174
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e174
            | exact resolve b7e174 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e174
          have b7e201 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e176
               grind)
            | exact superpose b7e176 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e176
          have b7e202 : y = (M.op y y) := by grind
          clear b7e201
          have b7e204 : False := by grind
          exact b7e204
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e81 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ x)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e129 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e89 (σ X0)
               grind)
            | exact superpose b8e89 b8e19
            | (have j1 := b8e89 (σ X0)
               grind)
            | exact resolve b8e19 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e21179 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e129 y
               grind)
            | exact superpose b8e129 b8e24
            | (have j1 := b8e129 y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e129 y
               grind)
            | exact resolve b8e24 b8e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e21276 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
          clear b8e21179
          have b8e21442 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e21276
               grind)
            | exact superpose b8e21276 b8e20
            | exact resolve b8e20 b8e21276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21276
          have b8e21878 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e21442
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e21442
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e21442 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21442
          have b8e21896 : y = (M.op y y) ∨ x = (M.op x x) := by grind
          clear b8e21878
          have b8e21906 : x = (M.op x x) := by
            first
            | (have r₁ := b8e21896
               have r₂ := b8e22
               grind)
            | exact resolve b8e21896 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21896
          have b8e21908 : False := by grind
          exact b8e21908

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_x_pxy_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
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
      have b0e35 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
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
      have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X0) X1)) := by
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
      have b0e43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op y X0) x
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e701 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X0 X0)) = (M.op X4 (M.op (M.op X5 X4) (M.op (M.op X1 X1) X0))) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b0e34 X1 (M.op x x) (M.op (M.op X1 X1) X0) X4 X5
           have i₂ := b0e38 X1 X0 x x
           grind)
        | exact superpose b0e38 b0e34
        | exact resolve b0e34 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e709 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op (M.op X0 X0) X0))) := by
        intro X0
        first
        | (have i₁ := b0e35 (M.op (M.op X0 X0) X0)
           have i₂ := b0e38 X0 X0 X0 X0
           grind)
        | exact superpose b0e38 b0e35
        | exact resolve b0e35 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e725 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op x (M.op y (M.op (M.op X1 X1) X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e701 X0 X1 x x
           have i₂ := b0e43 (M.op (M.op X1 X1) X0) x x
           grind)
        | exact superpose b0e43 b0e701
        | exact resolve b0e701 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e701
      have b0e1494 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e47 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e47
        | exact resolve b0e47 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e1808 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
        first
        | (have i₁ := b0e1494 x
           have i₂ := b0e35 (M.op y x)
           grind)
        | exact superpose b0e35 b0e1494
        | exact resolve b0e1494 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e1859 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e43 (M.op y X0) x y
           have i₂ := b0e1494 X0
           grind)
        | exact superpose b0e1494 b0e43
        | exact resolve b0e43 b0e1494
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e1494
      have b0e1923 : (M.op x x) = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b0e1808
           have i₂ := b0e1859 x
           grind)
        | exact superpose b0e1859 b0e1808
        | exact resolve b0e1808 b0e1859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1808 b0e1859
      have b0e1940 : y = (M.op x y) := by
        first
        | (have i₁ := b0e1923
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1923
        | exact resolve b0e1923 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1923
      have b0e20152 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e709 X0
           have i₂ := b0e725 X0 X0
           grind)
        | exact superpose b0e725 b0e709
        | exact resolve b0e709 b0e725
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e709 b0e725
      have b0e20898 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e20152 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e20152
        | exact resolve b0e20152 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20152
      have b0e21128 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20898
           grind)
        | exact superpose b0e20898 b0e18
        | exact resolve b0e18 b0e20898
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20898
      have b0e21161 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e21128
           have i₂ := b0e1940
           grind)
        | exact superpose b0e1940 b0e21128
        | exact resolve b0e21128 b0e1940
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1940 b0e21128
      have b0e21162 : False := by grind
      exact b0e21162
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : x = (k x y) := by grind
        have b1e26 : (σ y) = (k (σ y) (σ x)) := by grind
        have b1e27 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e26
          | exact resolve b1e26 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y x)
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e13
          | exact resolve b1e13 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e33 : y = (k y x) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e32
          | exact resolve b1e32 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e37 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
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
        have b1e46 : ∀ X0 : G, (k X0 (M.op x (M.op y X0))) = X0 := by
          intro X0
          grind
        have b1e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e91 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e92 : x = (M.op y y) ∨ (k y x) = (M.op y x) := by grind
        have b1e108 : x = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e92
             have i₂ := b1e33
             grind)
          | exact superpose b1e33 b1e92
          | exact resolve b1e92 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e92
        have b1e109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e91
             have r₂ := b1e21
             grind)
          | exact resolve b1e91 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91
        have b1e112 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e109
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e109
          | exact resolve b1e109 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109
        have b1e114 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e112
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e112
          | exact resolve b1e112 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e112
        have b1e116 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e114
             grind)
          | exact superpose b1e114 b1e19
          | exact resolve b1e19 b1e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e136 : y = (k y (M.op x x)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e46 y
             have i₂ := b1e108
             grind)
          | exact superpose b1e108 b1e46
          | exact resolve b1e46 b1e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e139 : x = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e37 y
             have i₂ := b1e108
             grind)
          | exact superpose b1e108 b1e37
          | exact resolve b1e37 b1e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e142 : y = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b1e139
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e139
          | exact resolve b1e139 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e144 : y = (k y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e136
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e136
          | exact resolve b1e136 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e136
        have b1e1046 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e144
             grind)
          | exact superpose b1e144 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e144
        have b1e1047 : y = (M.op y y) ∨ y = (M.op y x) := by grind
        clear b1e1046
        have b1e1262 : y = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e37 y
             have i₂ := b1e1047
             grind)
          | exact superpose b1e1047 b1e37
          | exact resolve b1e37 b1e1047
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1047
        have b1e1407 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e37 x
             have i₂ := b1e1262
             grind)
          | exact superpose b1e1262 b1e37
          | exact resolve b1e37 b1e1262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e1262
        have b1e1414 : y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e1407
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1407
          | exact resolve b1e1407 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1407
        have b1e1415 : y = (M.op x y) := by grind
        clear b1e1414
        have b1e1560 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e116
             have i₂ := b1e1415
             grind)
          | exact superpose b1e1415 b1e116
          | exact resolve b1e116 b1e1415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116
        have b1e1566 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e1415
             grind)
          | exact superpose b1e1415 b1e12
          | exact resolve b1e12 b1e1415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1415
        have b1e2232 : (M.op x x) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b1e1566 x
             have i₂ := b1e142
             grind)
          | exact superpose b1e142 b1e1566
          | exact resolve b1e1566 b1e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e142 b1e1566
        have b1e2335 : y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b1e2232
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2232
          | exact resolve b1e2232 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2232
        have b1e2754 : y = (k y y) ∨ x = y := by grind
        clear b1e2335
        have b1e4442 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e77 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e77
          | exact resolve b1e77 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e4762 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e4442
        have b1e4872 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e4762
             have r₂ := b1e1560
             grind)
          | exact resolve b1e4762 b1e1560
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4762
        have b1e4940 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e4872
             have i₂ := b1e2754
             grind)
          | exact superpose b1e2754 b1e4872
          | exact resolve b1e4872 b1e2754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2754 b1e4872
        have b1e4962 : x = y := by
          first
          | (have r₁ := b1e4940
             have r₂ := b1e1560
             grind)
          | exact resolve b1e4940 b1e1560
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4940
        have b1e5373 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1560
             have i₂ := b1e4962
             grind)
          | exact superpose b1e4962 b1e1560
          | exact resolve b1e1560 b1e4962
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1560 b1e4962
        have b1e5381 : False := by grind
        exact b1e5381
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e29 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y X0)) := by
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
        have b2e36 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op x (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op x (M.op y X0)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 X0
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op y X0) (M.op (M.op X0 X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op y X0) x
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e74 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e90 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e74 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e112 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e27 X1 X0
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e173 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e112
        have b2e190 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e173 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e173
          | exact resolve b2e173 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e173
        have b2e2589 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e40 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e40
          | exact resolve b2e40 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e3279 : (M.op x x) = (M.op x (M.op y (M.op y x))) := by
          first
          | (have i₁ := b2e2589 x
             have i₂ := b2e29 (M.op y x)
             grind)
          | exact superpose b2e29 b2e2589
          | exact resolve b2e2589 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e3351 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b2e36 (M.op y X0) x y
             have i₂ := b2e2589 X0
             grind)
          | exact superpose b2e2589 b2e36
          | exact resolve b2e36 b2e2589
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2589
        have b2e3447 : (M.op x x) = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b2e3279
             have i₂ := b2e3351 x
             grind)
          | exact superpose b2e3351 b2e3279
          | exact resolve b2e3279 b2e3351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3279 b2e3351
        have b2e3475 : y = (M.op x y) := by
          first
          | (have i₁ := b2e3447
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3447
          | exact resolve b2e3447 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3447
        have b2e3887 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e36 X0 y x
             have i₂ := b2e3475
             grind)
          | exact superpose b2e3475 b2e36
          | exact resolve b2e36 b2e3475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e5120 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e66 x x
             grind)
          | exact superpose b2e66 b2e21
          | (have j1 := b2e66 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e66 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e66 x y
             grind)
          | exact resolve b2e21 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5295 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e5296 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e5295 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5295
        have b2e5331 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e5120
        have b2e5519 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3887 (M.op (M.op x (M.op y y)) x)
             have i₂ := b2e38 y x
             grind)
          | exact superpose b2e38 b2e3887
          | exact resolve b2e3887 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e3887
        have b2e5960 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b2e5519 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5519
          | exact resolve b2e5519 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5519
        have b2e6030 : y = (M.op y y) := by
          first
          | (have i₁ := b2e5960
             have i₂ := b2e3475
             grind)
          | exact superpose b2e3475 b2e5960
          | exact resolve b2e5960 b2e3475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3475 b2e5960
        have b2e6487 : y = (k y y) := by grind
        clear b2e6030
        have b2e17104 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e5296 y
             have i₂ := b2e6487
             grind)
          | exact superpose b2e6487 b2e5296
          | (have j0 := b2e5296 y
             grind)
          | exact resolve b2e5296 b2e6487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5296 b2e6487
        have b2e17109 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e17104
        have b2e17151 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e17109
             grind)
          | exact superpose b2e17109 b2e22
          | exact resolve b2e22 b2e17109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17109
        have b2e17259 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5331
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e5331
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e5331 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5331
        have b2e17268 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e17259
        have b2e17285 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17268
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17268
          | exact resolve b2e17268 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17268
        have b2e17286 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e17285
        have b2e17297 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e17286
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17286
          | exact resolve b2e17286 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17286
        have b2e19332 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e190 x
             have i₂ := b2e17297
             grind)
          | exact superpose b2e17297 b2e190
          | exact resolve b2e190 b2e17297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e190 b2e17297
        have b2e19412 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e19332
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e19332
          | exact resolve b2e19332 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19332
        have b2e20050 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e90 x x
             have i₂ := b2e19412
             grind)
          | exact superpose b2e19412 b2e90
          | (have j0 := b2e90 x x
             grind)
          | exact resolve b2e90 b2e19412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90 b2e19412
        have b2e20051 : x = (M.op x x) ∨ x = y := by grind
        clear b2e20050
        have b2e20078 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e20051
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20051
          | exact resolve b2e20051 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20051
        have b2e20079 : x = y := by grind
        clear b2e20078
        have b2e21915 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e17151
             have i₂ := b2e20079
             grind)
          | exact superpose b2e20079 b2e17151
          | exact resolve b2e17151 b2e20079
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17151 b2e20079
        have b2e21918 : False := by grind
        exact b2e21918
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e27 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e26
          | exact resolve b3e26 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e32 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e13
          | exact resolve b3e13 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e33 : x = (k x y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e32
          | exact resolve b3e32 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e37 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) := by
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
        have b3e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b3e90 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e106 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e90
             have r₂ := b3e20
             grind)
          | exact resolve b3e90 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e110 : x = (M.op x y) := by
          first
          | (have i₁ := b3e106
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e106
          | exact resolve b3e106 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e106
        have b3e115 : (M.op y y) = (M.op y x) := by
          first
          | (have i₁ := b3e37 y
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e37
          | exact resolve b3e37 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e117 : x = (M.op y x) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e115
          | exact resolve b3e115 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115
        have b3e127 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e117
             grind)
          | exact superpose b3e117 b3e12
          | exact resolve b3e12 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117
        have b3e172 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e127 y
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e127
          | exact resolve b3e127 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110 b3e127
        have b3e186 : x = (M.op x x) := by
          first
          | (have i₁ := b3e172
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e172
          | exact resolve b3e172 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e172
        have b3e227 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e186
             grind)
          | exact superpose b3e186 b3e20
          | exact resolve b3e20 b3e186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e231 : x = (k x x) := by grind
        clear b3e186
        have b3e7000 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e75 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e75
          | exact resolve b3e75 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e7364 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e7000
        have b3e7494 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e7364
             have i₂ := b3e231
             grind)
          | exact superpose b3e231 b3e7364
          | exact resolve b3e7364 b3e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e231 b3e7364
        have b3e7495 : (σ x) = (σ y) := by grind
        clear b3e7494
        have b3e7658 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e7495
             grind)
          | exact superpose b3e7495 b3e13
          | exact resolve b3e13 b3e7495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7495
        have b3e7680 : x = y := by
          first
          | (have i₁ := b3e7658
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e7658
          | exact resolve b3e7658 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7658
        have b3e7689 : False := by grind
        exact b3e7689
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e93 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e94 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e110 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e94
               have r₂ := b4e21
               grind)
            | exact resolve b4e94 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e111 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e93
               have r₂ := b4e23
               grind)
            | exact resolve b4e93 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e114 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e111
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e111
            | exact resolve b4e111 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111
          have b4e116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e114
               have i₂ := b4e110
               grind)
            | exact superpose b4e110 b4e114
            | exact resolve b4e114 b4e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110 b4e114
          have b4e118 : False := by grind
          exact b4e118
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e37 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op x X0)) := by
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
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X1 (M.op X2 X3)) X0) X3 X2
               have i₂ := b5e13 X0 (M.op X2 X3) X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e37 X0
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op x X0) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op x X0) y
               have i₂ := b5e37 X0
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e85 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e101 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e85 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e29 X1 X0
               grind)
            | exact superpose b5e29 b5e14
            | exact resolve b5e14 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e288 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e117
          have b5e305 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e288 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e288
            | exact resolve b5e288 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e288
          have b5e1669 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e48 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e48
            | exact resolve b5e48 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e2154 : (M.op y y) = (M.op y (M.op x (M.op x y))) := by
            first
            | (have i₁ := b5e1669 y
               have i₂ := b5e37 (M.op x y)
               grind)
            | exact superpose b5e37 b5e1669
            | exact resolve b5e1669 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2210 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b5e44 (M.op x X0) y x
               have i₂ := b5e1669 X0
               grind)
            | exact superpose b5e1669 b5e44
            | exact resolve b5e44 b5e1669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2282 : (M.op y y) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b5e2154
               have i₂ := b5e2210 y
               grind)
            | exact superpose b5e2210 b5e2154
            | exact resolve b5e2154 b5e2210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2154 b5e2210
          have b5e2301 : x = (M.op y x) := by
            first
            | (have i₁ := b5e2282
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2282
            | exact resolve b5e2282 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2282
          have b5e2652 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e2301
               grind)
            | exact superpose b5e2301 b5e13
            | exact resolve b5e13 b5e2301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2659 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op (M.op (M.op X0 x) X1) (M.op (M.op X0 x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1 y x
               have i₂ := b5e2301
               grind)
            | exact superpose b5e2301 b5e41
            | exact resolve b5e41 b5e2301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e2661 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e44 X0 x y
               have i₂ := b5e2301
               grind)
            | exact superpose b5e2301 b5e44
            | exact resolve b5e44 b5e2301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2301
          have b5e2662 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op x (M.op (M.op X0 x) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2659 X0 X1
               have i₂ := b5e37 (M.op (M.op X0 x) X1)
               grind)
            | exact superpose b5e37 b5e2659
            | exact resolve b5e2659 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e2659
          have b5e2664 : ∀ X0 X1 : G, (M.op x (M.op X1 X1)) = (M.op x (M.op x (M.op (M.op X0 x) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2662 X0 X1
               have i₂ := b5e2661 (M.op (M.op X0 x) X1)
               grind)
            | exact superpose b5e2661 b5e2662
            | exact resolve b5e2662 b5e2661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2662
          have b5e2665 : ∀ X1 : G, (M.op x (M.op y (M.op x X1))) = (M.op x (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b5e2664 x X1
               have i₂ := b5e44 X1 x x
               grind)
            | exact superpose b5e44 b5e2664
            | exact resolve b5e2664 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e2664
          have b5e2666 : ∀ X1 : G, (M.op x (M.op X1 X1)) = (M.op x (M.op x (M.op x X1))) := by
            intro X1
            first
            | (have i₁ := b5e2665 X1
               have i₂ := b5e2661 X1
               grind)
            | exact superpose b5e2661 b5e2665
            | exact resolve b5e2665 b5e2661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2661 b5e2665
          have b5e3805 : (M.op y y) = (M.op x (M.op x (M.op x y))) := by
            first
            | (have i₁ := b5e1669 y
               have i₂ := b5e2652 (M.op x y)
               grind)
            | exact superpose b5e2652 b5e1669
            | exact resolve b5e1669 b5e2652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1669 b5e2652
          have b5e3838 : (M.op y y) = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e3805
               have i₂ := b5e2666 y
               grind)
            | exact superpose b5e2666 b5e3805
            | exact resolve b5e3805 b5e2666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2666 b5e3805
          have b5e3864 : x = (M.op x x) := by
            first
            | (have i₁ := b5e3838
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3838
            | exact resolve b5e3838 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3838
          have b5e4369 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e3864
               grind)
            | exact superpose b5e3864 b5e21
            | exact resolve b5e21 b5e3864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3864
          have b5e5641 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e73 y y
               grind)
            | exact superpose b5e73 b5e24
            | (have j1 := b5e73 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e73 y x
               grind)
            | exact resolve b5e24 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e5850 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e5641
          have b5e20189 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e5850
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e5850
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e5850 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5850
          have b5e20198 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e20189
          have b5e20215 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e20198
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20198
            | exact resolve b5e20198 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20198
          have b5e20216 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e20215
          have b5e20227 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e20216
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20216
            | exact resolve b5e20216 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20216
          have b5e20237 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b5e20227
               have r₂ := b5e4369
               grind)
            | exact resolve b5e20227 b5e4369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20227
          have b5e20649 : y = (k y (τ (σ y))) := by
            first
            | (have i₁ := b5e305 y
               have i₂ := b5e20237
               grind)
            | exact superpose b5e20237 b5e305
            | exact resolve b5e305 b5e20237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e305 b5e20237
          have b5e20730 : y = (k y y) := by
            first
            | (have i₁ := b5e20649
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e20649
            | exact resolve b5e20649 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20649
          have b5e22375 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e101 y y
               have i₂ := b5e20730
               grind)
            | exact superpose b5e20730 b5e101
            | (have j0 := b5e101 y y
               grind)
            | exact resolve b5e101 b5e20730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101 b5e20730
          have b5e22376 : y = (M.op y y) := by grind
          clear b5e22375
          have b5e22399 : x = y := by
            first
            | (have i₁ := b5e22376
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e22376
            | exact resolve b5e22376 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22376
          have b5e22419 : False := by grind
          exact b5e22419
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b6e80 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e26
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e26 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e81 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e80
             have r₂ := b6e20
             grind)
          | exact resolve b6e80 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e84 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e81
             have r₂ := b6e21
             grind)
          | exact resolve b6e81 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e88 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e102 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e88 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e7638 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e77 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e77
          | exact resolve b6e77 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e8056 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e7638
        have b6e8286 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e8056
             grind)
          | exact superpose b6e8056 b6e13
          | exact resolve b6e13 b6e8056
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e8304 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8286
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e8286
          | exact resolve b6e8286 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8286
        have b6e8701 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e102 x x
             have i₂ := b6e8304
             grind)
          | exact superpose b6e8304 b6e102
          | (have j0 := b6e102 x y
             grind)
          | exact resolve b6e102 b6e8304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102 b6e8304
        have b6e8702 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e8701
        have b6e8708 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e8702
             have r₂ := b6e20
             grind)
          | exact resolve b6e8702 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8702
        have b6e9173 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e8708
        have b6e10306 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8056
             have i₂ := b6e9173
             grind)
          | exact superpose b6e9173 b6e8056
          | exact resolve b6e8056 b6e9173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8056 b6e9173
        have b6e10331 : (σ x) = (σ y) := by grind
        clear b6e10306
        have b6e11117 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e10331
             grind)
          | exact superpose b6e10331 b6e19
          | exact resolve b6e19 b6e10331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e11124 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e10331
             grind)
          | exact superpose b6e10331 b6e13
          | exact resolve b6e13 b6e10331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e11146 : x = y := by
          first
          | (have i₁ := b6e11124
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e11124
          | exact resolve b6e11124 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11124
        have b6e11150 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e11117
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e11117
          | exact resolve b6e11117 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11117
        have b6e11158 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e11150
             have i₂ := b6e10331
             grind)
          | exact superpose b6e10331 b6e11150
          | exact resolve b6e11150 b6e10331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10331 b6e11150
        have b6e11165 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e11158
             have i₂ := b6e11146
             grind)
          | exact superpose b6e11146 b6e11158
          | exact resolve b6e11158 b6e11146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11158
        have b6e12175 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e84
             have i₂ := b6e11146
             grind)
          | exact superpose b6e11146 b6e84
          | exact resolve b6e84 b6e11146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e11146
        have b6e12186 : False := by grind
        exact b6e12186
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ y) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e27
            | exact resolve b7e27 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e33 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e28
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : y = (k y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e38 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X3)) := by
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
          have b7e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
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
          have b7e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X1 (M.op X2 X3)) X0)) = (M.op X3 (M.op X0 X0)) := by
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
          have b7e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e74 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e75 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e28
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e28 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e77 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e79 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e21
               grind)
            | exact resolve b7e76 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e80 : y = (M.op x y) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e21
               grind)
            | exact resolve b7e77 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e82 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e80
               grind)
            | exact superpose b7e80 b7e13
            | exact resolve b7e13 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e84 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e86 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b7e96 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e97 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e98 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e23
               grind)
            | exact resolve b7e86 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e100 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e98
            | exact resolve b7e98 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e113 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e30 X1 X0
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e130 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e20
            | exact resolve b7e20 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e131 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (k x y)) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e13
            | exact resolve b7e13 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e132 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e130
               have i₂ := b7e79
               grind)
            | exact superpose b7e79 b7e130
            | exact resolve b7e130 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e130
          have b7e133 : (σ y) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e132
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e132
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e132 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e132
          have b7e134 : (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e133
               have r₂ := b7e21
               grind)
            | exact resolve b7e133 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e135 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e134
               have r₂ := b7e22
               grind)
            | exact resolve b7e134 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e141 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b7e38 (σ y)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e38
            | exact resolve b7e38 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e159 : (σ x) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b7e141
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e141
            | exact resolve b7e141 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e793 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b7e113
          have b7e810 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e793 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e793
            | exact resolve b7e793 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e793
          have b7e847 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (k x y)) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ (k x y)) (σ y)
               have i₂ := b7e159
               grind)
            | exact superpose b7e159 b7e13
            | exact resolve b7e13 b7e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e159
          have b7e1286 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (M.op y x)) X0)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b7e131 X0
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e131
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e131 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1367 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (M.op y x)) X0)) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have j0 := b7e1286 X0
               grind)
            | (have r₁ := b7e1286 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e1286 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1286
          have b7e1395 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ (M.op y x)) X0)) := by
            intro X0
            first
            | (have j0 := b7e1367 X0
               grind)
            | (have r₁ := b7e1367 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e1367 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1367
          have b7e1482 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y y) ∨ (k x y) = (M.op y x) := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e96 y x
               grind)
            | exact superpose b7e96 b7e28
            | (have j1 := b7e96 y x
               grind)
            | exact resolve b7e28 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e96
          have b7e1508 : x = (M.op y y) ∨ (k x y) = (M.op y x) := by
            first
            | (have r₁ := b7e1482
               have r₂ := b7e135
               grind)
            | exact resolve b7e1482 b7e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135 b7e1482
          have b7e1532 : (k x y) = (M.op y x) := by
            first
            | (have r₁ := b7e1508
               have r₂ := b7e22
               grind)
            | exact resolve b7e1508 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1508
          have b7e1800 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e41 X0 X1 (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) x
               have i₂ := b7e39 X0 X1 (M.op X1 X0) x
               grind)
            | exact superpose b7e39 b7e41
            | exact resolve b7e41 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e41
          have b7e4450 : (M.op (σ y) (σ y)) = (M.op (σ (k x y)) (σ (k x y))) := by
            first
            | (have i₁ := b7e847 (σ y)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e847
            | exact resolve b7e847 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e4526 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e131 (M.op (σ x) X0)
               have i₂ := b7e847 X0
               grind)
            | exact superpose b7e847 b7e131
            | exact resolve b7e131 b7e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131 b7e847
          have b7e4553 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op y (M.op y (M.op (σ x) X0))) := by
            intro X0
            first
            | (have i₁ := b7e4526 X0
               have i₂ := b7e82 (M.op (σ x) X0)
               grind)
            | exact superpose b7e82 b7e4526
            | exact resolve b7e4526 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4526
          have b7e4623 : (M.op (σ y) (σ y)) = (M.op y (M.op y (σ (k x y)))) := by
            first
            | (have i₁ := b7e4450
               have i₂ := b7e82 (σ (k x y))
               grind)
            | exact superpose b7e82 b7e4450
            | exact resolve b7e4450 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4450
          have b7e4687 : (M.op (σ y) (σ y)) = (M.op y (M.op y (σ (M.op y x)))) := by
            first
            | (have i₁ := b7e4623
               have i₂ := b7e1532
               grind)
            | exact superpose b7e1532 b7e4623
            | exact resolve b7e4623 b7e1532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1532 b7e4623
          have b7e4703 : (σ x) = (M.op y (M.op y (σ (M.op y x)))) := by
            first
            | (have i₁ := b7e4687
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e4687
            | exact resolve b7e4687 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4687
          have b7e5089 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (M.op (σ (M.op y x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e42 X0 y y (σ (M.op y x))
               have i₂ := b7e4703
               grind)
            | exact superpose b7e4703 b7e42
            | exact resolve b7e42 b7e4703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e5110 : ∀ X0 : G, (M.op y (M.op y (M.op (σ x) X0))) = (M.op (σ (M.op y x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e5089 X0
               have i₂ := b7e82 (M.op (σ x) X0)
               grind)
            | exact superpose b7e82 b7e5089
            | exact resolve b7e5089 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5089
          have b7e6665 : (M.op y (M.op y (σ (M.op y x)))) = (M.op (σ y) (M.op y (M.op y (σ (M.op y x))))) := by
            first
            | (have i₁ := b7e1395 (σ (M.op y x))
               have i₂ := b7e82 (σ (M.op y x))
               grind)
            | exact superpose b7e82 b7e1395
            | exact resolve b7e1395 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e6752 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op y x)) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e1800 (σ y) (σ (M.op y x))
               have i₂ := b7e1395 (M.op (σ y) (σ y))
               grind)
            | exact superpose b7e1395 b7e1800
            | exact resolve b7e1800 b7e1395
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1395 b7e1800
          have b7e6784 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op y (M.op y (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b7e6752
               have i₂ := b7e5110 (σ y)
               grind)
            | exact superpose b7e5110 b7e6752
            | exact resolve b7e6752 b7e5110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5110 b7e6752
          have b7e6829 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e6665
               have i₂ := b7e4703
               grind)
            | exact superpose b7e4703 b7e6665
            | exact resolve b7e6665 b7e4703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4703 b7e6665
          have b7e6865 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e6784
               have i₂ := b7e4553 (σ y)
               grind)
            | exact superpose b7e4553 b7e6784
            | exact resolve b7e6784 b7e4553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4553 b7e6784
          have b7e6894 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e6865
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e6865
            | exact resolve b7e6865 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6865
          have b7e6905 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e6894
               have i₂ := b7e6829
               grind)
            | exact superpose b7e6829 b7e6894
            | exact resolve b7e6894 b7e6829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6829 b7e6894
          have b7e6928 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e72 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e72
            | exact resolve b7e72 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e7335 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e6928
          have b7e7628 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e6905
               grind)
            | exact superpose b7e6905 b7e23
            | exact resolve b7e23 b7e6905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7631 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b7e810 x
               have i₂ := b7e6905
               grind)
            | exact superpose b7e6905 b7e810
            | exact resolve b7e810 b7e6905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e810 b7e6905
          have b7e7683 : x = (k x x) := by
            first
            | (have i₁ := b7e7631
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e7631
            | exact resolve b7e7631 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7631
          have b7e8551 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e97 x x
               have i₂ := b7e7683
               grind)
            | exact superpose b7e7683 b7e97
            | (have j0 := b7e97 x x
               grind)
            | exact resolve b7e97 b7e7683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7683
          have b7e8552 : x = (M.op x x) := by grind
          clear b7e8551
          have b7e9009 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e8552
               grind)
            | exact superpose b7e8552 b7e21
            | exact resolve b7e21 b7e8552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8552
          have b7e11444 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e7335
               grind)
            | exact superpose b7e7335 b7e14
            | exact resolve b7e14 b7e7335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7335
          have b7e11466 : (τ (σ x)) = (k y y) := by
            first
            | (have r₁ := b7e11444
               have r₂ := b7e7628
               grind)
            | exact resolve b7e11444 b7e7628
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7628 b7e11444
          have b7e11487 : x = (k y y) := by
            first
            | (have i₁ := b7e11466
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e11466
            | exact resolve b7e11466 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11466
          have b7e11518 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e97 y y
               have i₂ := b7e11487
               grind)
            | exact superpose b7e11487 b7e97
            | (have j0 := b7e97 y x
               grind)
            | exact resolve b7e97 b7e11487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e11519 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b7e11518
          have b7e11525 : y = (M.op y y) := by
            first
            | (have r₁ := b7e11519
               have r₂ := b7e22
               grind)
            | exact resolve b7e11519 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11519
          have b7e12278 : y = (k y y) := by grind
          clear b7e11525
          have b7e12324 : x = y := by
            first
            | (have i₁ := b7e12278
               have i₂ := b7e11487
               grind)
            | exact superpose b7e11487 b7e12278
            | exact resolve b7e12278 b7e11487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11487 b7e12278
          have b7e12337 : False := by grind
          exact b7e12337
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e53 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) X0
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
          have b8e705 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e53 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e706 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e705
               have r₂ := b8e23
               grind)
            | exact resolve b8e705 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e705
          have b8e707 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e706
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e706
            | exact resolve b8e706 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e706
          have b8e708 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e707
               grind)
            | exact superpose b8e707 b8e20
            | exact resolve b8e20 b8e707
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e707
          have b8e723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e708
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e708
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e708 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e708
          have b8e724 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e723
          have b8e727 : y = (M.op x x) := by
            first
            | (have r₁ := b8e724
               have r₂ := b8e22
               grind)
            | exact resolve b8e724 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e724
          have b8e731 : False := by grind
          exact b8e731

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation3495 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e27
      have b0e88 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e95 : False := by grind
      exact b0e95
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
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
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e25
          | exact resolve b3e25 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : (M.op x x) = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e72 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = X0 ∨ (k X0 y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 x
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
          have b4e74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ x)
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
          have b4e77 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e74 X0
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e74
            | (have j0 := b4e74 X0
               grind)
            | exact resolve b4e74 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e788 : x = y ∨ (M.op x y) = (k x y) := by
            first
            | (have j0 := b4e72 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e789 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e788
               have r₂ := b4e21
               grind)
            | exact resolve b4e788 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e788
          have b4e2511 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e77 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e77
            | (have j0 := b4e77 (σ X0)
               grind)
            | (have r₁ := b4e77 (σ x)
               have r₂ := b4e30 x
               grind)
            | exact resolve b4e77 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e77
          have b4e2519 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e2511 X0
               have i₂ := b4e19 X0 y
               grind)
            | exact superpose b4e19 b4e2511
            | (have j0 := b4e2511 X0
               grind)
            | exact resolve b4e2511 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2511
          have b4e238095 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b4e2519 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2519
          have b4e238102 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b4e238095
               have r₂ := b4e23
               grind)
            | exact resolve b4e238095 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e238095
          have b4e238106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e238102
               have i₂ := b4e789
               grind)
            | exact superpose b4e789 b4e238102
            | exact resolve b4e238102 b4e789
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e789 b4e238102
          have b4e238110 : False := by grind
          exact b4e238110
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : (M.op x x) = (M.op y y) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e60 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e60
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e60
            | exact resolve b5e60 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e64 : False := by grind
          exact b5e64
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
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
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e62 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e62
            | exact resolve b7e62 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e62
          have b7e79 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e80 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e79
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e79
            | exact resolve b7e79 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e84 : False := by grind
          exact b7e84
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e59 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e59
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e59
            | exact resolve b8e59 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
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
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e100 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e78 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e78
            | (have j0 := b8e78 X0 X1
               grind)
            | exact resolve b8e78 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e100 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e100
            | (have j0 := b8e100 X0 X1
               grind)
            | exact resolve b8e100 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e100
          have b8e381 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e88 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e382 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e381
               have r₂ := b8e21
               grind)
            | exact resolve b8e381 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e381
          have b8e3127 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e102 x y
               grind)
            | exact superpose b8e102 b8e20
            | (have j1 := b8e102 y x
               grind)
            | exact resolve b8e20 b8e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e3197 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e3127
               have r₂ := b8e62
               grind)
            | exact resolve b8e3127 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62 b8e3127
          have b8e3231 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e3197
               have r₂ := b8e23
               grind)
            | exact resolve b8e3197 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3197
          have b8e3248 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e3231
               have i₂ := b8e382
               grind)
            | exact superpose b8e382 b8e3231
            | exact resolve b8e3231 b8e382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e382 b8e3231
          have b8e3249 : False := by grind
          exact b8e3249

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
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
        have b1e56 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e61 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e56
        have b1e62 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e61
             have r₂ := b1e23
             grind)
          | exact resolve b1e61 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e63 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e62
          | exact resolve b1e62 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e64 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e63
          | exact resolve b1e63 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e63
        have b1e65 : False := by grind
        exact b1e65
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
        have b2e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1249 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e18288 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1249 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1249
          | (have j0 := b2e1249 x y
             grind)
          | exact resolve b2e1249 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1249
        have b2e18299 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e18288
        have b2e18314 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e18299
             have r₂ := b2e22
             grind)
          | exact resolve b2e18299 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18299
        have b2e18324 : False := by grind
        exact b2e18324
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
        have b3e48 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e51 : x = y ∨ x = (k x y) := by grind
        clear b3e48
        have b3e52 : x = (k x y) := by
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
          have b5e55 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e60 : x = y ∨ x = (k x y) := by grind
          clear b5e55
          have b5e61 : x = (k x y) := by
            first
            | (have r₁ := b5e60
               have r₂ := b5e25
               grind)
            | exact resolve b5e60 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e60
          have b5e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e1237 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e64 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e18206 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1237 x y
               have i₂ := b5e61
               grind)
            | exact superpose b5e61 b5e1237
            | (have j0 := b5e1237 x y
               grind)
            | exact resolve b5e1237 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61 b5e1237
          have b5e18219 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e18206
          have b5e18258 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e18219
               have r₂ := b5e24
               grind)
            | exact resolve b5e18219 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18219
          have b5e18266 : False := by grind
          exact b5e18266
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
        have b6e63 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e65 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e63
        have b6e68 : x = (M.op x y) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e21
             grind)
          | exact resolve b6e65 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e71 : False := by grind
        exact b6e71
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
          have b7e51 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e56 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e51
          have b7e57 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e25
               grind)
            | exact resolve b7e56 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e56
          have b7e58 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e57
            | exact resolve b7e57 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e14
            | exact resolve b7e14 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e62 : x = (k x y) := by
            first
            | (have i₁ := b7e61
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e61
            | exact resolve b7e61 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e71 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e62
               grind)
            | exact superpose b7e62 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e72 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e71
          have b7e74 : y = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e76 : False := by grind
          exact b7e76
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
          have b8e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
               have i₂ := b8e57 x y
               grind)
            | exact superpose b8e57 b8e20
            | (have j1 := b8e57 x y
               grind)
            | exact resolve b8e20 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e1260 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1200
               have r₂ := b8e24
               grind)
            | exact resolve b8e1200 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1200
          have b8e1266 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1260
               have r₂ := b8e23
               grind)
            | exact resolve b8e1260 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1260
          have b8e1269 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1266
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1266
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1266 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1266
          have b8e1270 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e1269
          have b8e1271 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1270
               have r₂ := b8e22
               grind)
            | exact resolve b8e1270 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1270
          have b8e1272 : False := by grind
          exact b8e1272
