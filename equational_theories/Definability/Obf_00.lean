import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation433`: `x = x ◇ (y ◇ (x ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation433 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law433 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law433.models_iff G M).mp hM
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
          intro X0 X1 X2
          grind
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
        have b1e36 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op X0 X1) (M.op X0 X1)
             have i₂ := b1e12 (M.op X0 X1) X1 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e39 X0 (σ y)
             grind)
          | exact superpose b1e39 b1e36
          | exact resolve b1e36 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e39
        have b1e44 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e42 (σ x)
             grind)
          | exact superpose b1e42 b1e22
          | exact resolve b1e22 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e48 : False := by grind
        exact b1e48
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
        have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e199 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e2102 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e199 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e199
          | (have j0 := b2e199 x y
             grind)
          | exact resolve b2e199 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e199
        have b2e2107 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e2102
        have b2e2134 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2107
             have r₂ := b2e22
             grind)
          | exact resolve b2e2107 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2107
        have b2e2143 : False := by grind
        exact b2e2143
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x y) := by grind
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
        have b3e38 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 (M.op X0 X1) (M.op X0 X1)
             have i₂ := b3e12 (M.op X0 X1) X1 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e38 X0
             have i₂ := b3e42 X0 y
             grind)
          | exact superpose b3e42 b3e38
          | exact resolve b3e38 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e42
        have b3e47 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e45 x
             grind)
          | exact superpose b3e45 b3e21
          | exact resolve b3e21 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e51 : False := by grind
        exact b3e51
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x y) := by grind
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
          have b5e34 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X1) (M.op X0 X1)
               have i₂ := b5e13 (M.op X0 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e34 X0
               have i₂ := b5e37 X0 y
               grind)
            | exact superpose b5e37 b5e34
            | exact resolve b5e34 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e37
          have b5e42 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e40 x
               grind)
            | exact superpose b5e40 b5e22
            | exact resolve b5e22 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e46 : False := by grind
          exact b5e46
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
        have b6e51 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e53 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e51
        have b6e56 : x = (M.op x y) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e21
             grind)
          | exact resolve b6e53 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e59 : False := by grind
        exact b6e59
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
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
          have b7e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X1) (M.op X0 X1)
               have i₂ := b7e13 (M.op X0 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e30 X0
               have i₂ := b7e33 X0 (σ y)
               grind)
            | exact superpose b7e33 b7e30
            | exact resolve b7e30 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e33
          have b7e38 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e36 (σ x)
               grind)
            | exact superpose b7e36 b7e24
            | exact resolve b7e24 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e42 : False := by grind
          exact b7e42
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
          have b8e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e169 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e47 x y
               grind)
            | exact superpose b8e47 b8e20
            | (have j1 := b8e47 x y
               grind)
            | exact resolve b8e20 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47
          have b8e188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e169
               have r₂ := b8e24
               grind)
            | exact resolve b8e169 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e169
          have b8e191 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e188
               have r₂ := b8e23
               grind)
            | exact resolve b8e188 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188
          have b8e192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e191
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e191
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e191 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e191
          have b8e193 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e192
          have b8e194 : x = (M.op x y) := by
            first
            | (have r₁ := b8e193
               have r₂ := b8e22
               grind)
            | exact resolve b8e193 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e193
          have b8e195 : False := by grind
          exact b8e195

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4411 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4411 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e12
        | exact resolve b0e12 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X2 X0) X3
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X0 X3
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 X2 (M.op X2 X0)
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ y) X0) := by
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
      have b0e40 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
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
      have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e33 X0 X1 X2 X3
           have i₂ := b0e37 X2 X0 X3 X2
           grind)
        | exact superpose b0e37 b0e33
        | exact resolve b0e33 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e37
      have b0e43 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 x X1
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X1 X2
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X0 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e110 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e26 X1 X0
           grind)
        | exact superpose b0e26 b0e12
        | exact resolve b0e12 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e133 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e36 X2 X3 X4 (M.op X2 X0)
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e36
        | exact resolve b0e36 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e134 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 X0 X1 X2 (M.op X0 x)
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e36
        | exact resolve b0e36 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e142 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 y X0 X1 x
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e36
        | exact resolve b0e36 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e178 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e142 X0 X1
           have i₂ := b0e45 X1 y
           grind)
        | exact superpose b0e45 b0e142
        | exact resolve b0e142 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e142
      have b0e180 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e133 X0 X1 X2 X3 X4
           have i₂ := b0e134 (M.op X0 X1) X2 X4
           grind)
        | exact superpose b0e134 b0e133
        | exact resolve b0e133 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133
      have b0e190 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y y) X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e180 x x X2 X3 X4
           have i₂ := b0e134 y (M.op x x) X4
           grind)
        | (have i₁ := b0e180 x x X2 X3 X2
           have i₂ := b0e134 (M.op x x) x X2
           grind)
        | exact superpose b0e134 b0e180
        | exact resolve b0e180 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180
      have b0e193 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op y X4) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e190 X2 X3 X4
           have i₂ := b0e178 y X4
           grind)
        | exact superpose b0e178 b0e190
        | exact resolve b0e190 b0e178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e178 b0e190
      have b0e203 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e193 (σ x) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e193
        | exact resolve b0e193 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e214 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e193 X1 x X0
           grind)
        | exact superpose b0e193 b0e11
        | exact resolve b0e11 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e260 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e39 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e39
        | exact resolve b0e39 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e291 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e260
           have i₂ := b0e203 (σ x)
           grind)
        | exact superpose b0e203 b0e260
        | exact resolve b0e260 b0e203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e203 b0e260
      have b0e907 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X0) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X0 X3 X4
           have i₂ := b0e41 X1 X2 X0 X3
           grind)
        | (have i₁ := b0e11 (M.op X0 X1) (M.op X0 X1) X2
           have i₂ := b0e41 X0 X1 (M.op X0 X1) X3
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e933 : ∀ X0 X3 X4 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X3 X4) X0) := by
        intro X0 X3 X4
        first
        | (have i₁ := b0e907 X0 x x X3 X4
           have i₂ := b0e193 x x X0
           grind)
        | exact superpose b0e193 b0e907
        | exact resolve b0e907 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e907
      have b0e994 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e933 X0 x x
           have i₂ := b0e193 x x X0
           grind)
        | exact superpose b0e193 b0e933
        | exact resolve b0e933 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e933
      have b0e3739 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e68 X1 X0 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e3740 : ∀ X0 X1 : G, (M.op y X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e3739 X0 X1 x
           have i₂ := b0e193 X0 x X0
           grind)
        | exact superpose b0e193 b0e3739
        | (have j0 := b0e3739 X0 X1 x
           grind)
        | (have r₁ := b0e3739 x (M.op y x) x
           have r₂ := b0e193 x x x
           grind)
        | exact resolve b0e3739 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3739
      have b0e4814 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e291
           grind)
        | exact superpose b0e291 b0e18
        | exact resolve b0e18 b0e291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e291
      have b0e6247 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e16 (M.op X0 X1) X2
           have i₂ := b0e134 X0 X1 (M.op X0 X1)
           grind)
        | (have i₁ := b0e16 (M.op y X0) X1
           have i₂ := b0e134 X0 X1 (M.op y X0)
           grind)
        | exact superpose b0e134 b0e16
        | (have j0 := b0e16 (M.op X0 X1) X2
           grind)
        | exact resolve b0e16 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134
      have b0e6445 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6247 X0 X1 X2
           have i₂ := b0e193 y X0 (M.op X0 X1)
           grind)
        | exact superpose b0e193 b0e6247
        | (have j0 := b0e6247 X0 X1 X2
           grind)
        | exact resolve b0e6247 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6247
      have b0e6602 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e6445 X0 X1 X2
           have j1 := b0e3740 (M.op X0 X1) X2
           grind)
        | (have r₁ := b0e6445 X0 X1 X1
           have r₂ := b0e3740 (M.op X0 X1) X1
           grind)
        | (have r₁ := b0e6445 X0 X1 (M.op y X0)
           have r₂ := b0e3740 X0 (M.op y (M.op X0 X1))
           grind)
        | (have r₁ := b0e6445 X0 X1 (M.op y X0)
           have r₂ := b0e3740 X0 (M.op (M.op X0 X1) (M.op y X0))
           grind)
        | exact resolve b0e6445 b0e3740
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3740 b0e6445
      have b0e6726 : ∀ X0 X1 X2 : G, (M.op y X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6602 X0 X1 X2
           have i₂ := b0e193 X0 X1 X2
           grind)
        | exact superpose b0e193 b0e6602
        | (have j0 := b0e6602 X0 X1 X2
           grind)
        | exact resolve b0e6602 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6602
      have b0e6818 : ∀ X0 X1 X2 : G, (M.op y X2) = (k (M.op X0 X1) X2) ∨ (M.op y X2) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6726 X0 X1 X2
           have i₂ := b0e193 X0 X1 X2
           grind)
        | exact superpose b0e193 b0e6726
        | (have j0 := b0e6726 X0 X1 X2
           grind)
        | exact resolve b0e6726 b0e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e193 b0e6726
      have b0e13752 : ∀ X0 : G, (M.op y X0) = (k (σ y) X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e6818 (σ x) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e6818
        | (have j0 := b0e6818 X0 x X0
           grind)
        | exact resolve b0e6818 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e13757 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e6818 x x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e6818
        | (have j0 := b0e6818 X0 x X0
           grind)
        | exact resolve b0e6818 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6818
      have b0e14021 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k (τ y) X0) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e31 y X0
           have i₂ := b0e13757 (σ X0)
           grind)
        | exact superpose b0e13757 b0e31
        | (have j1 := b0e13757 (σ X0)
           grind)
        | exact resolve b0e31 b0e13757
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13757
      have b0e16343 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e110 y X0
           have i₂ := b0e13752 X0
           grind)
        | exact superpose b0e13752 b0e110
        | (have j1 := b0e13752 X0
           grind)
        | exact resolve b0e110 b0e13752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110
      have b0e16346 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 y X0
           have i₂ := b0e13752 (σ X0)
           grind)
        | exact superpose b0e13752 b0e17
        | (have j1 := b0e13752 (σ X0)
           grind)
        | exact resolve b0e17 b0e13752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e16361 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k (τ (σ y)) X0) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e31 (σ y) X0
           have i₂ := b0e13752 (σ X0)
           grind)
        | exact superpose b0e13752 b0e31
        | (have j1 := b0e13752 (σ X0)
           grind)
        | exact resolve b0e31 b0e13752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e13752
      have b0e16369 : ∀ X0 : G, (k y X0) = (τ (M.op y (σ X0))) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e16361 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e16361
        | (have j0 := b0e16361 X0
           grind)
        | exact resolve b0e16361 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16361
      have b0e26302 : (τ (M.op x y)) = (k y (τ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e16343 x
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e16343
        | exact resolve b0e16343 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16343
      have b0e27634 : (M.op x y) = (σ (k y (τ x))) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e13 (M.op x y)
           have i₂ := b0e26302
           grind)
        | exact superpose b0e26302 b0e13
        | exact resolve b0e13 b0e26302
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26302
      have b0e27648 : (M.op x y) = (k (σ y) x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e27634
           have i₂ := b0e26 x y
           grind)
        | exact superpose b0e26 b0e27634
        | exact resolve b0e27634 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27634
      have b0e61354 : ∀ X0 : G, (k y X0) = (k (τ y) X0) ∨ (σ X0) = (M.op y (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e16369 X0
           have i₂ := b0e14021 X0
           grind)
        | exact superpose b0e14021 b0e16369
        | (have j0 := b0e16369 X0
           have j1 := b0e14021 X0
           grind)
        | exact resolve b0e16369 b0e14021
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14021 b0e16369
      have b0e61386 : ∀ X0 : G, (k y X0) = (k (τ y) X0) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e61354 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61354
      have b0e68541 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (τ y)) X0) ∨ (σ (τ X0)) = (M.op y (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e26 X0 (τ y)
           have i₂ := b0e61386 (τ X0)
           grind)
        | exact superpose b0e61386 b0e26
        | (have j1 := b0e61386 (τ X0)
           grind)
        | exact resolve b0e26 b0e61386
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61386
      have b0e68576 : ∀ X0 : G, (k y X0) = (σ (k y (τ X0))) ∨ (σ (τ X0)) = (M.op y (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e68541 X0
           have i₂ := b0e13 y
           grind)
        | exact superpose b0e13 b0e68541
        | (have j0 := b0e68541 X0
           grind)
        | exact resolve b0e68541 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68541
      have b0e68638 : ∀ X0 : G, (k (σ y) X0) = (k y X0) ∨ (σ (τ X0)) = (M.op y (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e68576 X0
           have i₂ := b0e26 X0 y
           grind)
        | exact superpose b0e26 b0e68576
        | (have j0 := b0e68576 X0
           grind)
        | exact resolve b0e68576 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e68576
      have b0e68686 : ∀ X0 : G, (k (σ y) X0) = (k y X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e68638 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e68638
        | (have j0 := b0e68638 X0
           grind)
        | exact resolve b0e68638 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68638
      have b0e70119 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b0e27648
           have i₂ := b0e68686 x
           grind)
        | exact superpose b0e68686 b0e27648
        | (have j1 := b0e68686 x
           grind)
        | exact resolve b0e27648 b0e68686
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27648 b0e68686
      have b0e70259 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e70119
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e70119
        | exact resolve b0e70119 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70119
      have b0e70260 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
      clear b0e70259
      have b0e72187 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e16346 x
           have i₂ := b0e70260
           grind)
        | exact superpose b0e70260 b0e16346
        | (have j0 := b0e16346 x
           grind)
        | exact resolve b0e16346 b0e70260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16346 b0e70260
      have b0e72212 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e72187
           have r₂ := b0e4814
           grind)
        | exact resolve b0e72187 b0e4814
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4814 b0e72187
      have b0e73255 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e994 (σ x)
           have i₂ := b0e72212
           grind)
        | exact superpose b0e72212 b0e994
        | exact resolve b0e994 b0e72212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e994 b0e72212
      have b0e73360 : x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e73255
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e73255
        | exact resolve b0e73255 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73255
      have b0e74985 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e214 x y
           have i₂ := b0e73360
           grind)
        | exact superpose b0e73360 b0e214
        | exact resolve b0e214 b0e73360
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214
      have b0e75011 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e74985
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e74985
        | exact resolve b0e74985 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e74985
      have b0e75043 : y = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e75011
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e75011
        | exact resolve b0e75011 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75011
      have b0e77067 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e73360
           have i₂ := b0e75043
           grind)
        | exact superpose b0e75043 b0e73360
        | exact resolve b0e73360 b0e75043
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73360 b0e75043
      have b0e77117 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e77067
      have b0e77907 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e77117
           grind)
        | exact superpose b0e77117 b0e12
        | exact resolve b0e12 b0e77117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77117
      have b0e78014 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e77907
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e77907
        | exact resolve b0e77907 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77907
      have b0e78015 : x = y := by grind
      clear b0e78014
      have b0e80375 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e78015
           grind)
        | exact superpose b0e78015 b0e18
        | exact resolve b0e18 b0e78015
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78015
      have b0e80506 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e80375
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e80375
        | exact resolve b0e80375 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80375
      have b0e80544 : False := by grind
      exact b0e80544
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 X0 X3
             have i₂ := b1e12 X2 X0 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
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
        have b1e36 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) := by
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
        have b1e39 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e35 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e35
          | exact resolve b1e35 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x X1
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op X0 x)
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e55 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e12
          | exact resolve b1e12 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e56 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e55 X0
             have i₂ := b1e41 X0 y
             grind)
          | exact superpose b1e41 b1e55
          | exact resolve b1e55 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e55
        have b1e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e123 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 y X1
             have i₂ := b1e56 X0
             grind)
          | exact superpose b1e56 b1e12
          | exact resolve b1e12 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e141 : (σ y) = (M.op (M.op y (σ y)) (σ x)) := by
          first
          | (have i₁ := b1e36 (M.op (σ y) y)
             have i₂ := b1e56 (σ y)
             grind)
          | exact superpose b1e56 b1e36
          | exact resolve b1e36 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e151 : (σ y) = (M.op (σ x) (M.op (σ x) y)) := by
          first
          | (have i₁ := b1e141
             have i₂ := b1e12 (σ x) y (σ y)
             grind)
          | exact superpose b1e12 b1e141
          | exact resolve b1e141 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141
        have b1e156 : (σ y) = (M.op (M.op y y) (σ x)) := by
          first
          | (have i₁ := b1e151
             have i₂ := b1e42 y (σ x)
             grind)
          | exact superpose b1e42 b1e151
          | exact resolve b1e151 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e151
        have b1e161 : (σ y) = (M.op y (σ x)) := by
          first
          | (have i₁ := b1e156
             have i₂ := b1e123 (σ x) y
             grind)
          | exact superpose b1e123 b1e156
          | exact resolve b1e156 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e156
        have b1e196 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e31 X0 X1 X2 (M.op X0 y)
             have i₂ := b1e56 X0
             grind)
          | exact superpose b1e56 b1e31
          | exact resolve b1e31 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e56
        have b1e260 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e196 X0 X1 X2
             have i₂ := b1e123 X2 X0
             grind)
          | exact superpose b1e123 b1e196
          | exact resolve b1e196 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123 b1e196
        have b1e355 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op X0 (σ x))
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e368 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e355 X0 X1
             have i₂ := b1e260 (σ y) X0 X1
             grind)
          | exact superpose b1e260 b1e355
          | exact resolve b1e355 b1e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e260 b1e355
        have b1e4441 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e61 x x
             grind)
          | exact superpose b1e61 b1e21
          | (have j1 := b1e61 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e61 x y
             grind)
          | exact resolve b1e21 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e4512 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e4441
        have b1e12290 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e4512
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e4512
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e4512 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4512
        have b1e12291 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e12290
        have b1e12292 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e12291
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12291
          | exact resolve b1e12291 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12291
        have b1e12293 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e12292
        have b1e12299 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e12293
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12293
          | exact resolve b1e12293 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12293
        have b1e12343 : (M.op (σ x) (σ x)) = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e368 (σ x) (σ x)
             have i₂ := b1e12299
             grind)
          | exact superpose b1e12299 b1e368
          | exact resolve b1e368 b1e12299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e368 b1e12299
        have b1e12347 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e12343
             have i₂ := b1e161
             grind)
          | exact superpose b1e161 b1e12343
          | exact resolve b1e12343 b1e161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e161 b1e12343
        have b1e12375 : x = y := by
          first
          | (have r₁ := b1e12347
             have r₂ := b1e21
             grind)
          | exact resolve b1e12347 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12347
        have b1e12876 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e12375
             grind)
          | exact superpose b1e12375 b1e24
          | exact resolve b1e24 b1e12375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e12922 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e12876
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12876
          | exact resolve b1e12876 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12876
        have b1e12935 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e12922
             have i₂ := b1e12375
             grind)
          | exact superpose b1e12375 b1e12922
          | exact resolve b1e12922 b1e12375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12375 b1e12922
        have b1e12936 : False := by grind
        exact b1e12936
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
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
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X0 X3
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y X0) := by
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
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 X2 (M.op X2 X0)
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e30 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e30
          | exact resolve b2e30 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e12
          | exact resolve b2e12 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e48 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e47 X0
             have i₂ := b2e37 X0 y
             grind)
          | exact superpose b2e37 b2e47
          | exact resolve b2e47 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e72 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x X0) (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b2e30 (M.op x X0)
             have i₂ := b2e37 x X0
             grind)
          | exact superpose b2e37 b2e30
          | exact resolve b2e30 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e73 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e72 X0
             have i₂ := b2e37 (M.op y x) X0
             grind)
          | exact superpose b2e37 b2e72
          | exact resolve b2e72 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e72
        have b2e84 : ∀ X0 : G, (M.op y y) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e73 X0
             have i₂ := b2e30 y
             grind)
          | exact superpose b2e30 b2e73
          | exact resolve b2e73 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e115 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y X1
             have i₂ := b2e48 X0
             grind)
          | exact superpose b2e48 b2e12
          | exact resolve b2e12 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e147 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 X0 X1 (M.op (M.op X0 X1) x) X2
             have i₂ := b2e30 (M.op X0 X1)
             grind)
          | exact superpose b2e30 b2e29
          | exact resolve b2e29 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e152 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 X0 X1 X2 (M.op X0 y)
             have i₂ := b2e48 X0
             grind)
          | exact superpose b2e48 b2e29
          | exact resolve b2e29 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e207 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e152 X0 X1 X2
             have i₂ := b2e115 X2 X0
             grind)
          | exact superpose b2e115 b2e152
          | exact resolve b2e152 b2e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115 b2e152
        have b2e210 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op x (M.op x X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e147 X0 X1 X2
             have i₂ := b2e12 x X0 X1
             grind)
          | exact superpose b2e12 b2e147
          | exact resolve b2e147 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e147
        have b2e219 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op x (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e210 X0 X1 x
             have i₂ := b2e207 X0 x (M.op x (M.op x X0))
             grind)
          | exact superpose b2e207 b2e210
          | exact resolve b2e210 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e210
        have b2e220 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
          intro X0 X1
          first
          | (have i₁ := b2e219 X0 X1
             have i₂ := b2e84 (M.op x X0)
             grind)
          | exact superpose b2e84 b2e219
          | exact resolve b2e219 b2e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84 b2e219
        have b2e293 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e29 (M.op X2 X3) X1 X0 X4
             have i₂ := b2e31 X2 X3 X1 X0
             grind)
          | exact superpose b2e31 b2e29
          | exact resolve b2e29 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e31
        have b2e311 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e293 X0 X1 x x x
             have i₂ := b2e207 (M.op x x) x X0
             grind)
          | exact superpose b2e207 b2e293
          | exact resolve b2e293 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e293
        have b2e2138 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e58 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e2139 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2138
             have r₂ := b2e22
             grind)
          | exact resolve b2e2138 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2138
        have b2e2140 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2139
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2139
          | exact resolve b2e2139 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2139
        have b2e2141 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e2140
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e2140
          | exact resolve b2e2140 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e2140
        have b2e2143 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2141
             grind)
          | exact superpose b2e2141 b2e22
          | exact resolve b2e22 b2e2141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2155 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e207 (σ x) (σ y) X0
             have i₂ := b2e2141
             grind)
          | exact superpose b2e2141 b2e207
          | exact resolve b2e207 b2e2141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e207
        have b2e2156 : (M.op y y) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e220 (σ x) (σ y)
             have i₂ := b2e2141
             grind)
          | exact superpose b2e2141 b2e220
          | exact resolve b2e220 b2e2141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e220
        have b2e2157 : (M.op (σ x) (σ x)) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e311 (σ x) (σ y)
             have i₂ := b2e2141
             grind)
          | exact superpose b2e2141 b2e311
          | exact resolve b2e311 b2e2141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e311 b2e2141
        have b2e3434 : (σ x) = (k (σ x) (M.op y (σ x))) := by grind
        clear b2e2155
        have b2e3503 : (σ x) = (k (σ x) (M.op y y)) := by
          first
          | (have i₁ := b2e3434
             have i₂ := b2e2156
             grind)
          | exact superpose b2e2156 b2e3434
          | exact resolve b2e3434 b2e2156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3434
        have b2e3630 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e53 x x
             grind)
          | exact superpose b2e53 b2e21
          | (have j1 := b2e53 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e53 x y
             grind)
          | exact resolve b2e21 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e3696 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e3630
        have b2e3738 : (σ x) = (M.op y (σ x)) ∨ (σ y) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b2e3696
             have i₂ := b2e2157
             grind)
          | exact superpose b2e2157 b2e3696
          | exact resolve b2e3696 b2e2157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2157 b2e3696
        have b2e3772 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y y) := by
          first
          | (have i₁ := b2e3738
             have i₂ := b2e2156
             grind)
          | exact superpose b2e2156 b2e3738
          | exact resolve b2e3738 b2e2156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2156 b2e3738
        have b2e4450 : (k x (τ (M.op y y))) = (τ (σ x)) := by
          first
          | (have i₁ := b2e108 x (M.op y y)
             have i₂ := b2e3503
             grind)
          | exact superpose b2e3503 b2e108
          | exact resolve b2e108 b2e3503
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108 b2e3503
        have b2e4459 : x = (k x (τ (M.op y y))) := by
          first
          | (have i₁ := b2e4450
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e4450
          | exact resolve b2e4450 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4450
        have b2e7028 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e3772
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e3772
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e3772 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3772
        have b2e7029 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by grind
        clear b2e7028
        have b2e7030 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e7029
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7029
          | exact resolve b2e7029 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7029
        have b2e7031 : (σ x) = (M.op y y) ∨ x = (M.op x x) := by grind
        clear b2e7030
        have b2e7038 : (σ x) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e7031
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7031
          | exact resolve b2e7031 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7031
        have b2e7043 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e4459
             have i₂ := b2e7038
             grind)
          | exact superpose b2e7038 b2e4459
          | exact resolve b2e4459 b2e7038
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4459 b2e7038
        have b2e7101 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e7043
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e7043
          | exact resolve b2e7043 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7043
        have b2e7172 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e7101
             grind)
          | exact superpose b2e7101 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e7101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7101
        have b2e7173 : x = (M.op x x) ∨ x = y := by grind
        clear b2e7172
        have b2e7180 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e7173
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7173
          | exact resolve b2e7173 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7173
        have b2e7181 : x = y := by grind
        clear b2e7180
        have b2e7636 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e2143
             have i₂ := b2e7181
             grind)
          | exact superpose b2e7181 b2e2143
          | exact resolve b2e2143 b2e7181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2143 b2e7181
        have b2e7645 : False := by grind
        exact b2e7645
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 X0 X3
             have i₂ := b3e12 X2 X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1
             have i₂ := b3e48 X0
             grind)
          | exact superpose b3e48 b3e12
          | exact resolve b3e12 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e62 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b3e52 X0 (M.op x x)
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e52
          | exact resolve b3e52 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e170 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e44 X0 X1 X2 (M.op X0 x)
             have i₂ := b3e48 X0
             grind)
          | exact superpose b3e48 b3e44
          | exact resolve b3e44 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e201 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e62 X1
             have i₂ := b3e44 y x X1 X0
             grind)
          | (have i₁ := b3e62 X1
             have i₂ := b3e44 y X0 X1 x
             grind)
          | exact superpose b3e44 b3e62
          | exact resolve b3e62 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e62
        have b3e219 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e170 X0 X1 X2
             have i₂ := b3e201 X0 X2
             grind)
          | exact superpose b3e201 b3e170
          | exact resolve b3e170 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e170 b3e201
        have b3e249 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e219 X1 x X0
             grind)
          | exact superpose b3e219 b3e12
          | exact resolve b3e12 b3e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e219
        have b3e1578 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e249 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e249
          | exact resolve b3e249 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1651 : y = (M.op y x) := by
          first
          | (have i₁ := b3e1578
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1578
          | exact resolve b3e1578 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1578
        have b3e4297 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e92 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e92
          | exact resolve b3e92 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e4394 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e4297
        have b3e6149 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e4394
             grind)
          | exact superpose b3e4394 b3e13
          | exact resolve b3e13 b3e4394
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4394
        have b3e6166 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e6149
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e6149
          | exact resolve b3e6149 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6149
        have b3e6181 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e6166
             grind)
          | exact superpose b3e6166 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e6166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6166
        have b3e6182 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e6181
        have b3e6184 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e6182
             have r₂ := b3e20
             grind)
          | exact resolve b3e6182 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6182
        have b3e7107 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e249 x x
             have i₂ := b3e6184
             grind)
          | exact superpose b3e6184 b3e249
          | exact resolve b3e249 b3e6184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e249 b3e6184
        have b3e7108 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e7107
             have i₂ := b3e1651
             grind)
          | exact superpose b3e1651 b3e7107
          | exact resolve b3e7107 b3e1651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1651 b3e7107
        have b3e7122 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e7108
             have r₂ := b3e20
             grind)
          | exact resolve b3e7108 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7108
        have b3e7638 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e7122
             grind)
          | exact superpose b3e7122 b3e24
          | exact resolve b3e24 b3e7122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e7663 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e7638
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e7638
          | exact resolve b3e7638 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7638
        have b3e7668 : False := by grind
        exact b3e7668
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 X3
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 x)) := by
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
          have b5e42 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e38 (M.op X0 X1)
               have i₂ := b5e13 x X0 X1
               grind)
            | exact superpose b5e13 b5e38
            | exact resolve b5e38 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 x X1
               have i₂ := b5e38 X0
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e52 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e48
          have b5e53 : x = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e63 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X1 X2
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e65 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
            intro X0
            first
            | (have i₁ := b5e44 X0 (M.op x x)
               have i₂ := b5e38 x
               grind)
            | exact superpose b5e38 b5e44
            | exact resolve b5e44 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x X0) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e38 (M.op x X0)
               have i₂ := b5e44 x X0
               grind)
            | exact superpose b5e44 b5e38
            | exact resolve b5e38 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op y (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e78 X0
               have i₂ := b5e44 (M.op y x) X0
               grind)
            | exact superpose b5e44 b5e78
            | exact resolve b5e78 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e78
          have b5e89 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e38 y
               grind)
            | exact superpose b5e38 b5e79
            | exact resolve b5e79 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e152 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 X0 X1 (M.op (M.op X0 X1) x) X2
               have i₂ := b5e38 (M.op X0 X1)
               grind)
            | exact superpose b5e38 b5e37
            | exact resolve b5e37 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e155 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e37 X2 X3 X4 (M.op X2 X0)
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e37
            | exact resolve b5e37 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e156 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 X0 X1 X2 (M.op X0 x)
               have i₂ := b5e38 X0
               grind)
            | exact superpose b5e38 b5e37
            | exact resolve b5e37 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e184 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e65 X1
               have i₂ := b5e37 y x X1 X0
               grind)
            | (have i₁ := b5e65 X1
               have i₂ := b5e37 y X0 X1 x
               grind)
            | exact superpose b5e37 b5e65
            | exact resolve b5e65 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e65
          have b5e202 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e156 X0 X1 X2
               have i₂ := b5e184 X0 X2
               grind)
            | exact superpose b5e184 b5e156
            | exact resolve b5e156 b5e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e156 b5e184
          have b5e203 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op x (M.op x X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e152 X0 X1 X2
               have i₂ := b5e13 x X0 X1
               grind)
            | exact superpose b5e13 b5e152
            | exact resolve b5e152 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e152
          have b5e211 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e203 X0 X1 x
               have i₂ := b5e202 X0 x (M.op x (M.op x X0))
               grind)
            | exact superpose b5e202 b5e203
            | exact resolve b5e203 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e203
          have b5e212 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b5e211 X0 X1
               have i₂ := b5e89 (M.op x X0)
               grind)
            | exact superpose b5e89 b5e211
            | exact resolve b5e211 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e211
          have b5e230 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e202 X1 x X0
               grind)
            | exact superpose b5e202 b5e13
            | exact resolve b5e13 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e232 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b5e249 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e232 X0 X1
               have i₂ := b5e212 X0 X1
               grind)
            | exact superpose b5e212 b5e232
            | exact resolve b5e232 b5e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e232
          have b5e1820 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b5e230 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e230
            | exact resolve b5e230 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1894 : y = (M.op y x) := by
            first
            | (have i₁ := b5e1820
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1820
            | exact resolve b5e1820 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1820
          have b5e1979 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e1980 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1979
               have r₂ := b5e24
               grind)
            | exact resolve b5e1979 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1979
          have b5e1981 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1980
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1980
            | exact resolve b5e1980 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1980
          have b5e1982 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1981
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e1981
            | exact resolve b5e1981 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e1981
          have b5e1983 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1982
               grind)
            | exact superpose b5e1982 b5e24
            | exact resolve b5e24 b5e1982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1995 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e202 (σ x) (σ y) X0
               have i₂ := b5e1982
               grind)
            | exact superpose b5e1982 b5e202
            | exact resolve b5e202 b5e1982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1996 : (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e212 (σ x) (σ y)
               have i₂ := b5e1982
               grind)
            | exact superpose b5e1982 b5e212
            | exact resolve b5e212 b5e1982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2502 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e63 X1 X0 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e2503 : ∀ X0 X1 : G, (M.op y X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e2502 X0 X1 x
               have i₂ := b5e202 X0 x X0
               grind)
            | exact superpose b5e202 b5e2502
            | (have j0 := b5e2502 X0 X1 x
               grind)
            | (have r₁ := b5e2502 x (M.op y x) X1
               have r₂ := b5e202 x X1 x
               grind)
            | exact resolve b5e2502 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2502
          have b5e2757 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1995 (σ x)
               grind)
            | exact superpose b5e1995 b5e23
            | exact resolve b5e23 b5e1995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2758 : (σ x) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e1982
               have i₂ := b5e1995 (σ y)
               grind)
            | exact superpose b5e1995 b5e1982
            | exact resolve b5e1982 b5e1995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1982 b5e1995
          have b5e2822 : (σ y) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e2757
               have i₂ := b5e1996
               grind)
            | exact superpose b5e1996 b5e2757
            | exact resolve b5e2757 b5e1996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1996 b5e2757
          have b5e3485 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e57 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e3487 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e3485 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3485
          have b5e5555 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X4 ∨ (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) X4) ∨ (M.op (M.op X2 X3) X4) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e18 (M.op X2 X3) X4
               have i₂ := b5e155 X0 X1 X2 X3 (M.op X2 X3)
               grind)
            | (have i₁ := b5e18 (M.op (M.op X0 X1) X2) X1
               have i₂ := b5e155 X0 X1 X2 X3 (M.op (M.op X0 X1) X2)
               grind)
            | exact superpose b5e155 b5e18
            | (have j0 := b5e18 (M.op X2 X3) X4
               grind)
            | exact resolve b5e18 b5e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e155
          have b5e5642 : ∀ X2 X3 X4 : G, (M.op y (M.op X2 X3)) = X4 ∨ (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) X4) ∨ (M.op (M.op X2 X3) X4) = X4 := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e5555 x x X2 X3 X4
               have i₂ := b5e202 (M.op x x) X2 (M.op X2 X3)
               grind)
            | exact superpose b5e202 b5e5555
            | (have j0 := b5e5555 x x X2 X3 X4
               grind)
            | exact resolve b5e5555 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5555
          have b5e5833 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) X4) ∨ (M.op (M.op X2 X3) X4) = X4 := by
            intro X2 X3 X4
            first
            | (have j0 := b5e5642 X2 X3 X4
               have j1 := b5e2503 (M.op X2 X3) X4
               grind)
            | (have r₁ := b5e5642 X2 X3 x
               have r₂ := b5e2503 (M.op X2 X3) x
               grind)
            | (have r₁ := b5e5642 X2 X3 (M.op y x)
               have r₂ := b5e2503 x (M.op y (M.op X2 X3))
               grind)
            | (have r₁ := b5e5642 X2 X3 (M.op y x)
               have r₂ := b5e2503 x (M.op (M.op X2 X3) (M.op y x))
               grind)
            | exact resolve b5e5642 b5e2503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5642
          have b5e5937 : ∀ X2 X3 X4 : G, (M.op y X4) = (k (M.op X2 X3) X4) ∨ (M.op (M.op X2 X3) X4) = X4 := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e5833 X2 X3 X4
               have i₂ := b5e202 X2 X3 X4
               grind)
            | exact superpose b5e202 b5e5833
            | (have j0 := b5e5833 X2 X3 X4
               grind)
            | exact resolve b5e5833 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5833
          have b5e6028 : ∀ X2 X3 X4 : G, (M.op y X4) = (k (M.op X2 X3) X4) ∨ (M.op y X4) = X4 := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e5937 X2 X3 X4
               have i₂ := b5e202 X2 X3 X4
               grind)
            | exact superpose b5e202 b5e5937
            | (have j0 := b5e5937 X2 X3 X4
               grind)
            | exact resolve b5e5937 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5937
          have b5e7602 : ∀ X0 : G, (M.op y (M.op x (M.op x x))) = X0 ∨ (M.op (M.op x (M.op x x)) X0) = (k (M.op x (M.op x x)) X0) ∨ (M.op (M.op x (M.op x x)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e18 (M.op x (M.op x x)) X0
               have i₂ := b5e42 x (M.op x x)
               grind)
            | exact superpose b5e42 b5e18
            | (have j0 := b5e18 (M.op x (M.op x x)) X0
               grind)
            | exact resolve b5e18 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e7646 : ∀ X0 : G, (M.op (M.op x (M.op x x)) X0) = (k (M.op x (M.op x x)) X0) ∨ (M.op (M.op x (M.op x x)) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e7602 X0
               have j1 := b5e2503 (M.op x (M.op x x)) X0
               grind)
            | (have r₁ := b5e7602 x
               have r₂ := b5e2503 (M.op x (M.op x x)) x
               grind)
            | (have r₁ := b5e7602 (M.op y X0)
               have r₂ := b5e2503 X0 (M.op y (M.op x (M.op x x)))
               grind)
            | (have r₁ := b5e7602 (M.op y X0)
               have r₂ := b5e2503 X0 (M.op (M.op x (M.op x x)) (M.op y X0))
               grind)
            | exact resolve b5e7602 b5e2503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2503 b5e7602
          have b5e7746 : ∀ X0 : G, (M.op (M.op y x) X0) = (k (M.op y x) X0) ∨ (M.op (M.op x (M.op x x)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7646 X0
               have i₂ := b5e38 x
               grind)
            | exact superpose b5e38 b5e7646
            | (have j0 := b5e7646 X0
               grind)
            | exact resolve b5e7646 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e7646
          have b5e7835 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op (M.op x (M.op x x)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7746 X0
               have i₂ := b5e1894
               grind)
            | exact superpose b5e1894 b5e7746
            | (have j0 := b5e7746 X0
               grind)
            | exact resolve b5e7746 b5e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7746
          have b5e7860 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e7835 X0
               have i₂ := b5e202 x (M.op x x) X0
               grind)
            | exact superpose b5e202 b5e7835
            | (have j0 := b5e7835 X0
               grind)
            | exact resolve b5e7835 b5e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e202 b5e7835
          have b5e7891 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k (τ y) X0) ∨ (σ X0) = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e33 y X0
               have i₂ := b5e7860 (σ X0)
               grind)
            | exact superpose b5e7860 b5e33
            | (have j1 := b5e7860 (σ X0)
               grind)
            | exact resolve b5e33 b5e7860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7860
          have b5e11895 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e3487 (M.op y y)
               have i₂ := b5e249 y y
               grind)
            | exact superpose b5e249 b5e3487
            | (have j0 := b5e3487 (M.op y y)
               grind)
            | exact resolve b5e3487 b5e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3487
          have b5e11903 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e11895
          have b5e16144 : (M.op y y) = (M.op y (σ (M.op y y))) := by
            first
            | (have i₁ := b5e212 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e11903
               grind)
            | exact superpose b5e11903 b5e212
            | exact resolve b5e212 b5e11903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16145 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op y (σ (M.op y y))) := by
            first
            | (have i₁ := b5e230 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e11903
               grind)
            | exact superpose b5e11903 b5e230
            | exact resolve b5e230 b5e11903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e230
          have b5e16149 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
            first
            | (have i₁ := b5e16145
               have i₂ := b5e11903
               grind)
            | exact superpose b5e11903 b5e16145
            | exact resolve b5e16145 b5e11903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11903 b5e16145
          have b5e16194 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e16149
               have i₂ := b5e16144
               grind)
            | exact superpose b5e16144 b5e16149
            | exact resolve b5e16149 b5e16144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16144 b5e16149
          have b5e16256 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e16194
               grind)
            | exact superpose b5e16194 b5e14
            | exact resolve b5e14 b5e16194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16257 : ∀ X0 : G, (σ (k (M.op y y) X0)) = (k (M.op y y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 (M.op y y) X0
               have i₂ := b5e16194
               grind)
            | exact superpose b5e16194 b5e19
            | exact resolve b5e19 b5e16194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16263 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e33 X0 (M.op y y)
               have i₂ := b5e16194
               grind)
            | exact superpose b5e16194 b5e33
            | exact resolve b5e33 b5e16194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e16194
          have b5e20071 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16263 (M.op X0 X1)
               have i₂ := b5e249 X0 X1
               grind)
            | exact superpose b5e249 b5e16263
            | exact resolve b5e16263 b5e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e249 b5e16263
          have b5e84874 : (τ (σ x)) = (k (τ y) y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e7891 y
               have i₂ := b5e2758
               grind)
            | exact superpose b5e2758 b5e7891
            | exact resolve b5e7891 b5e2758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2758 b5e7891
          have b5e84915 : (τ (σ x)) = (k (τ y) y) := by
            first
            | (have r₁ := b5e84874
               have r₂ := b5e1983
               grind)
            | exact resolve b5e84874 b5e1983
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84874
          have b5e84925 : x = (k (τ y) y) := by
            first
            | (have i₁ := b5e84915
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e84915
            | exact resolve b5e84915 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84915
          have b5e85259 : y = (M.op (τ y) y) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by
            first
            | (have i₁ := b5e60 y (τ y)
               have i₂ := b5e84925
               grind)
            | exact superpose b5e84925 b5e60
            | (have j0 := b5e60 y (τ y)
               grind)
            | exact resolve b5e60 b5e84925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e89272 : y ≠ y ∨ y = (M.op (τ y) (τ y)) ∨ (τ y) = (k (τ y) y) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by
            first
            | (have i₁ := b5e17 (τ y) y
               have i₂ := b5e85259
               grind)
            | exact superpose b5e85259 b5e17
            | (have j0 := b5e17 (τ y) y
               grind)
            | (have r₁ := b5e17 (τ y) y
               have r₂ := b5e85259
               grind)
            | exact resolve b5e17 b5e85259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85259
          have b5e89316 : y = (M.op (τ y) (τ y)) ∨ (τ y) = (k (τ y) y) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by grind
          clear b5e89272
          have b5e89339 : x = (τ y) ∨ y = (M.op (τ y) (τ y)) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by
            first
            | (have i₁ := b5e89316
               have i₂ := b5e84925
               grind)
            | exact superpose b5e84925 b5e89316
            | exact resolve b5e89316 b5e84925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89316
          have b5e89340 : y = (M.op (τ y) (τ y)) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by grind
          clear b5e89339
          have b5e95813 : (τ y) = (k (τ y) y) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by grind
          clear b5e89340
          have b5e95884 : x = (τ y) ∨ x = (τ y) ∨ x = (M.op (τ y) y) := by
            first
            | (have i₁ := b5e95813
               have i₂ := b5e84925
               grind)
            | exact superpose b5e84925 b5e95813
            | exact resolve b5e95813 b5e84925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95813
          have b5e95885 : x = (M.op (τ y) y) ∨ x = (τ y) := by grind
          clear b5e95884
          have b5e95974 : (M.op y x) = (M.op y y) ∨ x = (τ y) := by
            first
            | (have i₁ := b5e212 (τ y) y
               have i₂ := b5e95885
               grind)
            | exact superpose b5e95885 b5e212
            | exact resolve b5e212 b5e95885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e212 b5e95885
          have b5e95999 : y = (M.op y y) ∨ x = (τ y) := by
            first
            | (have i₁ := b5e95974
               have i₂ := b5e1894
               grind)
            | exact superpose b5e1894 b5e95974
            | exact resolve b5e95974 b5e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95974
          have b5e96398 : (τ y) = (k (τ y) y) ∨ x = (τ y) := by
            first
            | (have i₁ := b5e20071 y y
               have i₂ := b5e95999
               grind)
            | exact superpose b5e95999 b5e20071
            | exact resolve b5e20071 b5e95999
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20071 b5e95999
          have b5e96411 : x = (τ y) ∨ x = (τ y) := by
            first
            | (have i₁ := b5e96398
               have i₂ := b5e84925
               grind)
            | exact superpose b5e84925 b5e96398
            | exact resolve b5e96398 b5e84925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84925 b5e96398
          have b5e96412 : x = (τ y) := by grind
          clear b5e96411
          have b5e96648 : y = (σ x) := by
            first
            | (have i₁ := b5e15 y
               have i₂ := b5e96412
               grind)
            | exact superpose b5e96412 b5e15
            | exact resolve b5e15 b5e96412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e96943 : (k (M.op y y) y) = (σ (k (M.op y y) x)) := by
            first
            | (have i₁ := b5e16257 x
               have i₂ := b5e96648
               grind)
            | exact superpose b5e96648 b5e16257
            | exact resolve b5e16257 b5e96648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16257 b5e96648
          have b5e102973 : (σ (M.op y x)) = (k (M.op y y) y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b5e96943
               have i₂ := b5e6028 y y x
               grind)
            | exact superpose b5e6028 b5e96943
            | (have j1 := b5e6028 x x x
               grind)
            | exact resolve b5e96943 b5e6028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96943
          have b5e103056 : (σ y) = (k (M.op y y) y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b5e102973
               have i₂ := b5e1894
               grind)
            | exact superpose b5e1894 b5e102973
            | exact resolve b5e102973 b5e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102973
          have b5e103080 : (σ y) = (k (M.op y y) y) ∨ x = y := by
            first
            | (have i₁ := b5e103056
               have i₂ := b5e1894
               grind)
            | exact superpose b5e1894 b5e103056
            | exact resolve b5e103056 b5e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1894 b5e103056
          have b5e103220 : (σ y) = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b5e6028 y y y
               have i₂ := b5e103080
               grind)
            | exact superpose b5e103080 b5e6028
            | (have j0 := b5e6028 x x y
               grind)
            | exact resolve b5e6028 b5e103080
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6028 b5e103080
          have b5e103255 : y = (M.op y y) ∨ x = y := by
            first
            | (have r₁ := b5e103220
               have r₂ := b5e2822
               grind)
            | exact resolve b5e103220 b5e2822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2822 b5e103220
          have b5e103328 : y = (τ y) ∨ x = y := by
            first
            | (have i₁ := b5e16256
               have i₂ := b5e103255
               grind)
            | exact superpose b5e103255 b5e16256
            | exact resolve b5e16256 b5e103255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16256 b5e103255
          have b5e103473 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e103328
               have i₂ := b5e96412
               grind)
            | exact superpose b5e96412 b5e103328
            | exact resolve b5e103328 b5e96412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96412 b5e103328
          have b5e103474 : x = y := by grind
          clear b5e103473
          have b5e103543 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1983
               have i₂ := b5e103474
               grind)
            | exact superpose b5e103474 b5e1983
            | exact resolve b5e1983 b5e103474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1983 b5e103474
          have b5e103713 : False := by grind
          exact b5e103713
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
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
        have b6e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X1 X2) X0 X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 X0 X3
             have i₂ := b6e12 X2 X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X3 X2 (M.op X2 X0)
             have i₂ := b6e12 X2 X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e77 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e85 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e77
             have r₂ := b6e20
             grind)
          | exact resolve b6e77 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e88 : x = (M.op x y) := by
          first
          | (have r₁ := b6e85
             have r₂ := b6e21
             grind)
          | exact resolve b6e85 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e90 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e88
             grind)
          | exact superpose b6e88 b6e21
          | exact resolve b6e21 b6e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e92 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e88
             grind)
          | exact superpose b6e88 b6e12
          | exact resolve b6e12 b6e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e111 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 x X0 X1 y
             have i₂ := b6e88
             grind)
          | exact superpose b6e88 b6e43
          | exact resolve b6e43 b6e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e197 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e43 X0 (M.op X0 x) X1 X2
             have i₂ := b6e92 X0
             grind)
          | exact superpose b6e92 b6e43
          | exact resolve b6e43 b6e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e199 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 x)
             have i₂ := b6e92 X0
             grind)
          | exact superpose b6e92 b6e12
          | exact resolve b6e12 b6e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e208 : ∀ X0 X1 : G, (M.op x X1) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e199 X0 X1
             have i₂ := b6e111 X0 X1
             grind)
          | exact superpose b6e111 b6e199
          | exact resolve b6e199 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199
        have b6e209 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e197 X0 X1 X2
             have i₂ := b6e111 X0 X1
             grind)
          | exact superpose b6e111 b6e197
          | exact resolve b6e197 b6e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111 b6e197
        have b6e266 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X3 X5) (M.op (M.op X3 X4) X2)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b6e43 X3 X4 (M.op (M.op X3 X4) X2) X5
             have i₂ := b6e45 X0 X1 X2 (M.op X3 X4)
             grind)
          | exact superpose b6e45 b6e43
          | exact resolve b6e43 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e45
        have b6e287 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op (M.op X3 X4) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e266 X0 X1 X2 X3 X4 x
             have i₂ := b6e209 X3 (M.op (M.op X3 X4) X2) x
             grind)
          | exact superpose b6e209 b6e266
          | exact resolve b6e266 b6e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e266
        have b6e321 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op x X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e287 X0 X1 X2 X3 X4
             have i₂ := b6e209 X3 X2 X4
             grind)
          | exact superpose b6e209 b6e287
          | exact resolve b6e287 b6e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e287
        have b6e342 : ∀ X0 X1 X2 X3 X4 : G, (M.op x x) = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e321 X0 X1 X2 X3 X4
             have i₂ := b6e208 X2 x
             grind)
          | exact superpose b6e208 b6e321
          | exact resolve b6e321 b6e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e208 b6e321
        have b6e358 : ∀ X3 X4 : G, (M.op x x) = (M.op x (M.op X3 X4)) := by
          intro X3 X4
          first
          | (have i₁ := b6e342 x x x X3 X4
             have i₂ := b6e209 (M.op x x) (M.op X3 X4) x
             grind)
          | exact superpose b6e209 b6e342
          | exact resolve b6e342 b6e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e342
        have b6e1125 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X0)))) := by
          intro X0 X1
          grind
        clear b6e42
        have b6e1190 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x (M.op X0 (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b6e1125 X0 X1
             have i₂ := b6e209 X0 (M.op X0 (M.op X0 X0)) X1
             grind)
          | exact superpose b6e209 b6e1125
          | exact resolve b6e1125 b6e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e209 b6e1125
        have b6e1302 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e1190 X0 X1
             have i₂ := b6e358 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e358 b6e1190
          | exact resolve b6e1190 b6e358
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e358 b6e1190
        have b6e3383 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e75 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e75
          | exact resolve b6e75 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e3477 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3383
        have b6e7253 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3477
             grind)
          | exact superpose b6e3477 b6e13
          | exact resolve b6e13 b6e3477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e7270 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e7253
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e7253
          | exact resolve b6e7253 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7253
        have b6e8189 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e7270
             grind)
          | exact superpose b6e7270 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e7270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7270
        have b6e8190 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e8189
        have b6e8192 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e8190
             have r₂ := b6e20
             grind)
          | exact resolve b6e8190 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8190
        have b6e8299 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1302 x x
             have i₂ := b6e8192
             grind)
          | exact superpose b6e8192 b6e1302
          | exact resolve b6e1302 b6e8192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1302 b6e8192
        have b6e8373 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3477
             have i₂ := b6e8299
             grind)
          | exact superpose b6e8299 b6e3477
          | exact resolve b6e3477 b6e8299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3477 b6e8299
        have b6e8380 : (σ x) = (σ y) := by grind
        clear b6e8373
        have b6e8461 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e8380
             grind)
          | exact superpose b6e8380 b6e13
          | exact resolve b6e13 b6e8380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8380
        have b6e8481 : x = y := by
          first
          | (have i₁ := b6e8461
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e8461
          | exact resolve b6e8461 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8461
        have b6e8494 : False := by grind
        exact b6e8494
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
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
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b7e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e29 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X1 X2) X0 X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X0 X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X2 (M.op X2 X0)
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e29 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e44 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (σ x) = (σ (k x y)) := by
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
          have b7e52 : (k x y) = (τ (σ x)) := by
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
          have b7e53 : x = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e63 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 X2
               have i₂ := b7e18 X2 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X2 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X1 X2
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
          have b7e70 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : x = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e22
               grind)
            | exact resolve b7e70 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e83 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e26
            | exact resolve b7e26 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e86 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e13
            | exact resolve b7e13 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e118 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 x X0 X1 y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e32
            | exact resolve b7e32 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e151 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e32 X0 (M.op X0 (σ x)) X1 X2
               have i₂ := b7e33 X0
               grind)
            | exact superpose b7e33 b7e32
            | exact resolve b7e32 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e190 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 x y X1 X0
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e34
            | exact resolve b7e34 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e229 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e190 X0 X1
               have i₂ := b7e118 X1 X0
               grind)
            | exact superpose b7e118 b7e190
            | exact resolve b7e190 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e190
          have b7e245 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e86 (M.op X0 X1)
               have i₂ := b7e13 x X0 X1
               grind)
            | exact superpose b7e13 b7e86
            | exact resolve b7e86 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e253 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X0) = (M.op X0 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X0 x) X1
               have i₂ := b7e86 X0
               grind)
            | exact superpose b7e86 b7e13
            | exact resolve b7e13 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e257 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e32 X0 X1 X2 (M.op X0 x)
               have i₂ := b7e86 X0
               grind)
            | exact superpose b7e86 b7e32
            | exact resolve b7e32 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e263 : (σ y) = (M.op (M.op x (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e37 (M.op (σ y) x)
               have i₂ := b7e86 (σ y)
               grind)
            | exact superpose b7e86 b7e37
            | exact resolve b7e37 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e264 : (σ y) = (M.op (σ x) (M.op (σ x) x)) := by
            first
            | (have i₁ := b7e263
               have i₂ := b7e13 (σ x) x (σ y)
               grind)
            | exact superpose b7e13 b7e263
            | exact resolve b7e263 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e263
          have b7e269 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e257 X0 X1 X2
               have i₂ := b7e118 X0 X2
               grind)
            | exact superpose b7e118 b7e257
            | exact resolve b7e257 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118 b7e257
          have b7e272 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e253 X0 X1
               have i₂ := b7e34 X0 x X1 X0
               grind)
            | exact superpose b7e34 b7e253
            | exact resolve b7e253 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e253
          have b7e278 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e245 X0 X1
               have i₂ := b7e229 x X0
               grind)
            | exact superpose b7e229 b7e245
            | exact resolve b7e245 b7e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e245
          have b7e281 : (σ y) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e264
               have i₂ := b7e86 (σ x)
               grind)
            | exact superpose b7e86 b7e264
            | exact resolve b7e264 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e264
          have b7e286 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e272 X0 x
               have i₂ := b7e229 X0 x
               grind)
            | exact superpose b7e229 b7e272
            | exact resolve b7e272 b7e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e272
          have b7e290 : ∀ X0 X1 : G, (M.op x (M.op x x)) = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e278 X0 X1
               have i₂ := b7e269 X0 X1 (M.op x x)
               grind)
            | exact superpose b7e269 b7e278
            | exact resolve b7e278 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e278
          have b7e298 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e290 X0 X1
               have i₂ := b7e86 x
               grind)
            | exact superpose b7e86 b7e290
            | exact resolve b7e290 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86 b7e290
          have b7e983 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            grind
          clear b7e31
          have b7e1043 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e983 X0 X1
               have i₂ := b7e269 X0 X1 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b7e269 b7e983
            | exact resolve b7e983 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e983
          have b7e1138 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e1043 X0 X1
               have i₂ := b7e298 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e298 b7e1043
            | exact resolve b7e1043 b7e298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1043
          have b7e1766 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (M.op X2 (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e63 (σ X1) X2 (σ X0)
               grind)
            | exact superpose b7e63 b7e19
            | (have j1 := b7e63 (σ X1) X2 (σ X0)
               grind)
            | exact resolve b7e19 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e1769 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op x X2) = (M.op (σ X1) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e1766 X0 X1 X2
               have i₂ := b7e229 X2 (σ X0)
               grind)
            | exact superpose b7e229 b7e1766
            | (have j0 := b7e1766 X0 X1 X2
               grind)
            | exact resolve b7e1766 b7e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e229 b7e1766
          have b7e2268 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e64 X1 X0 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e2269 : ∀ X0 X1 : G, (M.op x X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e2268 X0 X1 x
               have i₂ := b7e269 X0 x X0
               grind)
            | exact superpose b7e269 b7e2268
            | (have j0 := b7e2268 X0 X1 x
               grind)
            | (have r₁ := b7e2268 x (M.op x x) X1
               have r₂ := b7e269 x X1 x
               grind)
            | exact resolve b7e2268 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2268
          have b7e2523 : x = (M.op y x) := by
            first
            | (have i₁ := b7e286 y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e286
            | exact resolve b7e286 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e286
          have b7e3275 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e58 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e3277 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e3275 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3275
          have b7e4253 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e18 (M.op X0 X1) X2
               have i₂ := b7e151 X0 (M.op X0 X1) X1
               grind)
            | (have i₁ := b7e18 (M.op (σ y) X0) X1
               have i₂ := b7e151 X0 (M.op (σ y) X0) X2
               grind)
            | exact superpose b7e151 b7e18
            | (have j0 := b7e18 (M.op X0 X1) X2
               grind)
            | exact resolve b7e18 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e4329 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = X2 ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e4253 X0 X1 X2
               have i₂ := b7e269 (σ y) X0 (M.op X0 X1)
               grind)
            | exact superpose b7e269 b7e4253
            | (have j0 := b7e4253 X0 X1 X2
               grind)
            | exact resolve b7e4253 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4253
          have b7e4485 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e4329 X0 X1 X2
               have j1 := b7e2269 (M.op X0 X1) X2
               grind)
            | (have r₁ := b7e4329 X0 X1 X1
               have r₂ := b7e2269 (M.op X0 X1) X1
               grind)
            | (have r₁ := b7e4329 X0 X1 (M.op x X0)
               have r₂ := b7e2269 X0 (M.op x (M.op X0 X1))
               grind)
            | (have r₁ := b7e4329 X0 X1 (M.op x X0)
               have r₂ := b7e2269 X0 (M.op (M.op X0 X1) (M.op x X0))
               grind)
            | exact resolve b7e4329 b7e2269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2269 b7e4329
          have b7e4587 : ∀ X0 X1 X2 : G, (M.op x X2) = (k (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e4485 X0 X1 X2
               have i₂ := b7e269 X0 X1 X2
               grind)
            | exact superpose b7e269 b7e4485
            | (have j0 := b7e4485 X0 X1 X2
               grind)
            | exact resolve b7e4485 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4485
          have b7e4646 : ∀ X0 X1 X2 : G, (M.op x X2) = (k (M.op X0 X1) X2) ∨ (M.op x X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e4587 X0 X1 X2
               have i₂ := b7e269 X0 X1 X2
               grind)
            | exact superpose b7e269 b7e4587
            | (have j0 := b7e4587 X0 X1 X2
               grind)
            | exact resolve b7e4587 b7e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4587
          have b7e9432 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e4646 y x X0
               have i₂ := b7e2523
               grind)
            | exact superpose b7e2523 b7e4646
            | (have j0 := b7e4646 X0 x X0
               grind)
            | exact resolve b7e4646 b7e2523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2523
          have b7e9551 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ x) X0) ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e42 x X0
               have i₂ := b7e9432 (σ X0)
               grind)
            | exact superpose b7e9432 b7e42
            | (have j1 := b7e9432 (σ X0)
               grind)
            | exact resolve b7e42 b7e9432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9432
          have b7e15028 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e3277 (M.op x x)
               have i₂ := b7e1138 x x
               grind)
            | exact superpose b7e1138 b7e3277
            | (have j0 := b7e3277 (M.op x x)
               grind)
            | exact resolve b7e3277 b7e1138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3277
          have b7e15037 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
          clear b7e15028
          have b7e16184 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e269 (σ (M.op x x)) (σ (M.op x x)) X0
               have i₂ := b7e15037
               grind)
            | exact superpose b7e15037 b7e269
            | exact resolve b7e269 b7e15037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e269
          have b7e16185 : (M.op x x) = (M.op x (σ (M.op x x))) := by
            first
            | (have i₁ := b7e298 (σ (M.op x x)) (σ (M.op x x))
               have i₂ := b7e15037
               grind)
            | exact superpose b7e15037 b7e298
            | exact resolve b7e298 b7e15037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e16723 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
            first
            | (have i₁ := b7e15037
               have i₂ := b7e16184 (σ (M.op x x))
               grind)
            | exact superpose b7e16184 b7e15037
            | exact resolve b7e15037 b7e16184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e15037
          have b7e16861 : (M.op x x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e16723
               have i₂ := b7e16185
               grind)
            | exact superpose b7e16185 b7e16723
            | exact resolve b7e16723 b7e16185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e16185 b7e16723
          have b7e18774 : ∀ X0 : G, (τ (k X0 (M.op x x))) = (k (τ X0) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b7e42 X0 (M.op x x)
               have i₂ := b7e16861
               grind)
            | exact superpose b7e16861 b7e42
            | exact resolve b7e42 b7e16861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e31407 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) (M.op x x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e18774 (M.op X0 X1)
               have i₂ := b7e1138 X0 X1
               grind)
            | exact superpose b7e1138 b7e18774
            | exact resolve b7e18774 b7e1138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1138 b7e18774
          have b7e59520 : ∀ X0 : G, (σ y) ≠ (M.op x (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e1769 X0 x (σ x)
               grind)
            | exact superpose b7e1769 b7e23
            | (have j1 := b7e1769 X0 x x
               grind)
            | exact resolve b7e23 b7e1769
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1769
          have b7e59742 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have j0 := b7e59520 X0
               grind)
            | (have r₁ := b7e59520 X0
               have r₂ := b7e281
               grind)
            | exact resolve b7e59520 b7e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59520
          have b7e63882 : (τ (σ y)) = (k (τ x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e9551 x
               have i₂ := b7e281
               grind)
            | exact superpose b7e281 b7e9551
            | exact resolve b7e9551 b7e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9551
          have b7e63925 : (τ (σ y)) = (k (τ x) x) := by
            first
            | (have r₁ := b7e63882
               have r₂ := b7e83
               grind)
            | exact resolve b7e63882 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63882
          have b7e63932 : y = (k (τ x) x) := by
            first
            | (have i₁ := b7e63925
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e63925
            | exact resolve b7e63925 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63925
          have b7e64031 : y = (M.op (τ x) x) ∨ y = (τ x) ∨ x = (M.op (τ x) x) := by
            first
            | (have i₁ := b7e61 x (τ x)
               have i₂ := b7e63932
               grind)
            | exact superpose b7e63932 b7e61
            | (have j0 := b7e61 x (τ x)
               grind)
            | exact resolve b7e61 b7e63932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e80983 : (M.op x y) = (M.op x x) ∨ y = (τ x) ∨ x = (M.op (τ x) x) := by
            first
            | (have i₁ := b7e298 (τ x) x
               have i₂ := b7e64031
               grind)
            | exact superpose b7e64031 b7e298
            | exact resolve b7e298 b7e64031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e298 b7e64031
          have b7e81001 : x = (M.op (τ x) x) ∨ y = (τ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e80983
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e80983
            | exact resolve b7e80983 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e80983
          have b7e81414 : x ≠ x ∨ x = (M.op (τ x) (τ x)) ∨ (τ x) = (k (τ x) x) ∨ y = (τ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e17 (τ x) x
               have i₂ := b7e81001
               grind)
            | exact superpose b7e81001 b7e17
            | (have j0 := b7e17 (τ x) x
               grind)
            | (have r₁ := b7e17 (τ x) x
               have r₂ := b7e81001
               grind)
            | (have r₁ := b7e17 x x
               have r₂ := b7e81001
               grind)
            | exact resolve b7e17 b7e81001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81001
          have b7e81489 : x = (M.op (τ x) (τ x)) ∨ (τ x) = (k (τ x) x) ∨ y = (τ x) ∨ x = (M.op x x) := by grind
          clear b7e81414
          have b7e81541 : y = (τ x) ∨ x = (M.op (τ x) (τ x)) ∨ y = (τ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e81489
               have i₂ := b7e63932
               grind)
            | exact superpose b7e63932 b7e81489
            | exact resolve b7e81489 b7e63932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81489
          have b7e81542 : x = (M.op (τ x) (τ x)) ∨ y = (τ x) ∨ x = (M.op x x) := by grind
          clear b7e81541
          have b7e87848 : (τ x) = (k (τ x) x) ∨ y = (τ x) ∨ x = (M.op x x) := by grind
          clear b7e81542
          have b7e87990 : y = (τ x) ∨ y = (τ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e87848
               have i₂ := b7e63932
               grind)
            | exact superpose b7e63932 b7e87848
            | exact resolve b7e87848 b7e63932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87848
          have b7e87991 : x = (M.op x x) ∨ y = (τ x) := by grind
          clear b7e87990
          have b7e90545 : (τ x) = (k (τ x) x) ∨ y = (τ x) := by
            first
            | (have i₁ := b7e31407 x x
               have i₂ := b7e87991
               grind)
            | exact superpose b7e87991 b7e31407
            | exact resolve b7e31407 b7e87991
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31407 b7e87991
          have b7e90548 : y = (τ x) ∨ y = (τ x) := by
            first
            | (have i₁ := b7e90545
               have i₂ := b7e63932
               grind)
            | exact superpose b7e63932 b7e90545
            | exact resolve b7e90545 b7e63932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63932 b7e90545
          have b7e90549 : y = (τ x) := by grind
          clear b7e90548
          have b7e90881 : x = (σ y) := by
            first
            | (have i₁ := b7e15 x
               have i₂ := b7e90549
               grind)
            | exact superpose b7e90549 b7e15
            | exact resolve b7e15 b7e90549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90549
          have b7e91433 : x ≠ (σ x) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e90881
               grind)
            | exact superpose b7e90881 b7e83
            | exact resolve b7e83 b7e90881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e118208 : (M.op x (σ x)) = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b7e16184 (σ x)
               have i₂ := b7e59742 (M.op x x)
               grind)
            | exact superpose b7e59742 b7e16184
            | (have j1 := b7e59742 (M.op x x)
               grind)
            | exact resolve b7e16184 b7e59742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59742
          have b7e118412 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b7e118208
               have i₂ := b7e281
               grind)
            | exact superpose b7e281 b7e118208
            | exact resolve b7e118208 b7e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118208
          have b7e118497 : x = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b7e118412
               have i₂ := b7e90881
               grind)
            | exact superpose b7e90881 b7e118412
            | exact resolve b7e118412 b7e90881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90881 b7e118412
          have b7e118550 : (σ x) = (M.op x (σ x)) ∨ x = (σ (k (M.op x x) x)) := by
            first
            | (have i₁ := b7e118497
               have i₂ := b7e16184 (σ x)
               grind)
            | exact superpose b7e16184 b7e118497
            | exact resolve b7e118497 b7e16184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e16184 b7e118497
          have b7e118571 : (σ x) = (σ y) ∨ x = (σ (k (M.op x x) x)) := by
            first
            | (have i₁ := b7e118550
               have i₂ := b7e281
               grind)
            | exact superpose b7e281 b7e118550
            | exact resolve b7e118550 b7e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e281 b7e118550
          have b7e118589 : x = (σ (k (M.op x x) x)) := by
            first
            | (have r₁ := b7e118571
               have r₂ := b7e83
               grind)
            | exact resolve b7e118571 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e118571
          have b7e118629 : x = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e118589
               have i₂ := b7e4646 x x x
               grind)
            | exact superpose b7e4646 b7e118589
            | (have j1 := b7e4646 x x x
               grind)
            | exact resolve b7e118589 b7e4646
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4646 b7e118589
          have b7e118802 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e118629
               have i₂ := b7e16861
               grind)
            | exact superpose b7e16861 b7e118629
            | exact resolve b7e118629 b7e16861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118629
          have b7e118803 : x = (M.op x x) := by grind
          clear b7e118802
          have b7e119153 : x = (σ x) := by
            first
            | (have i₁ := b7e16861
               have i₂ := b7e118803
               grind)
            | exact superpose b7e118803 b7e16861
            | exact resolve b7e16861 b7e118803
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e16861 b7e118803
          have b7e119309 : False := by grind
          exact b7e119309
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e716 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e59 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e717 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e716
               have r₂ := b8e24
               grind)
            | exact resolve b8e716 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e716
          have b8e718 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e717
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e717
            | exact resolve b8e717 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e717
          have b8e719 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e718
               grind)
            | exact superpose b8e718 b8e20
            | exact resolve b8e20 b8e718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e718
          have b8e1121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e719
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e719
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e719 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e719
          have b8e1122 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1121
          have b8e1124 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1122
               have r₂ := b8e21
               grind)
            | exact resolve b8e1122 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1122
          have b8e1126 : False := by grind
          exact b8e1126

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxx_x_pxy_Equation4485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ y) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
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
        have b1e38 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (σ y)
             have i₂ := b1e37 X0
             grind)
          | (have i₁ := b1e12 X0 (σ y) X0
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e46 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e41 X0 X1
             have i₂ := b1e32 X1 X0
             grind)
          | exact superpose b1e32 b1e41
          | exact resolve b1e41 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e41
        have b1e50 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
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
        have b1e54 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e50
        have b1e56 : (σ y) = (σ (k y y)) := by
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
        have b1e69 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e13
          | exact resolve b1e13 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e70 : y = (k y y) := by
          first
          | (have i₁ := b1e69
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e69
          | exact resolve b1e69 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e103 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e104 : y = (M.op y y) := by grind
        clear b1e103
        have b1e109 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x X1
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e12
          | exact resolve b1e12 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e114 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op x x)
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e12
          | exact resolve b1e12 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e117 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e114 X0 X1
             have i₂ := b1e46 X0 X1
             grind)
          | exact superpose b1e46 b1e114
          | exact resolve b1e114 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e122 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b1e117 x X1
             have i₂ := b1e109 X1 x
             grind)
          | exact superpose b1e109 b1e117
          | exact resolve b1e117 b1e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109 b1e117
        have b1e132 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e104
             grind)
          | exact superpose b1e104 b1e12
          | exact resolve b1e12 b1e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e148 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 X1
             have i₂ := b1e132 (M.op X0 X1)
             grind)
          | exact superpose b1e132 b1e12
          | exact resolve b1e12 b1e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e132
        have b1e154 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e148 X0 X1
             have i₂ := b1e46 X0 y
             grind)
          | exact superpose b1e46 b1e148
          | exact resolve b1e148 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e148
        have b1e158 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e154 X0 X1
             have i₂ := b1e122 y
             grind)
          | exact superpose b1e122 b1e154
          | exact resolve b1e154 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122 b1e154
        have b1e160 : ∀ X0 X1 : G, x = (M.op y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e158 X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e158
          | exact resolve b1e158 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e158
        have b1e366 : x = (M.op y y) := by
          first
          | (have i₁ := b1e160 y y
             have i₂ := b1e104
             grind)
          | exact superpose b1e104 b1e160
          | exact resolve b1e160 b1e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160
        have b1e379 : x = y := by
          first
          | (have i₁ := b1e366
             have i₂ := b1e104
             grind)
          | exact superpose b1e104 b1e366
          | exact resolve b1e366 b1e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104 b1e366
        have b1e399 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e379
             grind)
          | exact superpose b1e379 b1e21
          | exact resolve b1e21 b1e379
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e379
        have b1e401 : False := by grind
        exact b1e401
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e24 X0 X1
             grind)
          | exact superpose b2e24 b2e13
          | exact resolve b2e13 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X0 X3
             have i₂ := b2e12 X2 X0 X1
             grind)
          | (have i₁ := b2e12 (M.op X1 X2) X1 X2
             have i₂ := b2e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op x X0) := by
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
        have b2e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 X2 (M.op X0 X0)
             have i₂ := b2e12 X2 X0 X1
             grind)
          | (have i₁ := b2e12 X0 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e12
          | exact resolve b2e12 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | (have i₁ := b2e15 X0 (M.op X1 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op X1 X2) X0
             grind)
          | (have r₁ := b2e15 (M.op X0 (M.op X0 X0)) X0
             have r₂ := b2e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 : G, (M.op x x) ≠ (M.op x (M.op x x)) ∨ (M.op X0 (M.op x x)) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 (M.op x x)
             have i₂ := b2e34 (M.op x x)
             grind)
          | exact superpose b2e34 b2e16
          | (have j0 := b2e16 X0 (M.op x x)
             grind)
          | exact resolve b2e16 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e52 X0
             grind)
          | (have r₁ := b2e52 X0
             have r₂ := b2e34 x
             grind)
          | exact resolve b2e52 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e55 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e54
          | (have j0 := b2e54 X0
             grind)
          | exact resolve b2e54 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e65 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e34 (M.op x X0)
             have i₂ := b2e40 (M.op x x) X0
             grind)
          | exact superpose b2e40 b2e34
          | exact resolve b2e34 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e70 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e65 X0
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e65
          | exact resolve b2e65 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e93 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e93 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e89 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e25 X1 X0
             grind)
          | exact superpose b2e25 b2e13
          | exact resolve b2e13 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e114 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e29 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e29
          | exact resolve b2e29 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e142 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e32 X0 X1 X2 (M.op x x)
             have i₂ := b2e34 X0
             grind)
          | exact superpose b2e34 b2e32
          | exact resolve b2e32 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e179 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e142 X0 X1 X2
             have i₂ := b2e40 X2 X0
             grind)
          | exact superpose b2e40 b2e142
          | exact resolve b2e142 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e142
        have b2e205 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e179 X1 x X0
             grind)
          | exact superpose b2e179 b2e12
          | exact resolve b2e12 b2e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e210 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (M.op x x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 (M.op X0 X1)
             have i₂ := b2e179 X0 X1 (M.op x x)
             grind)
          | exact superpose b2e179 b2e34
          | exact resolve b2e34 b2e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e219 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e210 X0 X1
             have i₂ := b2e70 x
             grind)
          | exact superpose b2e70 b2e210
          | exact resolve b2e210 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70 b2e210
        have b2e304 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op (M.op X2 X3) X1) ∨ (k (M.op (M.op X2 X3) X1) X0) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 (M.op (M.op X2 X3) X1) X0
             have i₂ := b2e35 X2 X3 X1 X0
             grind)
          | (have i₁ := b2e15 X3 (M.op X2 X2)
             have i₂ := b2e35 X0 X1 X2 X3
             grind)
          | exact superpose b2e35 b2e15
          | (have j0 := b2e15 (M.op (M.op X2 X3) X1) X0
             grind)
          | exact resolve b2e15 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e307 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op x X1) ∨ (k (M.op (M.op X2 X3) X1) X0) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e304 X0 X1 X2 X3
             have i₂ := b2e179 X2 X3 X1
             grind)
          | exact superpose b2e179 b2e304
          | (have j0 := b2e304 X0 X1 X2 X3
             grind)
          | exact resolve b2e304 b2e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e304
        have b2e357 : ∀ X0 X1 X2 X3 : G, (M.op x X0) ≠ (M.op x X1) ∨ (k (M.op (M.op X2 X3) X1) X0) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e307 X0 X1 X2 X3
             have i₂ := b2e205 X0 X1
             grind)
          | exact superpose b2e205 b2e307
          | (have j0 := b2e307 X0 X1 X2 X3
             grind)
          | (have r₁ := b2e307 X0 X0 X2 X3
             have r₂ := b2e205 X0 X0
             grind)
          | exact resolve b2e307 b2e205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e307
        have b2e391 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X2 X3) X1) X0) = (M.op x (M.op (M.op X2 X3) X1)) ∨ (M.op x X0) ≠ (M.op x X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e357 X0 X1 X2 X3
             have i₂ := b2e179 (M.op X2 X3) X1 (M.op (M.op X2 X3) X1)
             grind)
          | exact superpose b2e179 b2e357
          | (have j0 := b2e357 X0 X1 X2 X3
             grind)
          | exact resolve b2e357 b2e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e357
        have b2e414 : ∀ X0 X1 X2 X3 : G, (M.op x x) = (k (M.op (M.op X2 X3) X1) X0) ∨ (M.op x X0) ≠ (M.op x X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e391 X0 X1 X2 X3
             have i₂ := b2e219 (M.op X2 X3) X1
             grind)
          | exact superpose b2e219 b2e391
          | (have j0 := b2e391 X0 X1 X2 X3
             grind)
          | (have r₁ := b2e391 x (M.op X0 X1) X2 X3
             have r₂ := b2e219 X0 X1
             grind)
          | (have r₁ := b2e391 (M.op X0 X1) x X2 X3
             have r₂ := b2e219 X0 X1
             grind)
          | exact resolve b2e391 b2e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e391
        have b2e418 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ (M.op x x) = (k (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e414 X0 X1 x x
             have i₂ := b2e179 x x X1
             grind)
          | exact superpose b2e179 b2e414
          | (have j0 := b2e414 X0 X1 x x
             grind)
          | exact resolve b2e414 b2e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e414
        have b2e902 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e94 (σ X0)
             grind)
          | exact superpose b2e94 b2e18
          | (have j1 := b2e94 (σ X0)
             grind)
          | exact resolve b2e18 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3337 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e24 X0 (τ X0)
             have i₂ := b2e95 (τ X0) X1
             grind)
          | exact superpose b2e95 b2e24
          | (have j1 := b2e95 (τ X0) X1
             grind)
          | exact resolve b2e24 b2e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e3346 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (k X0 X0) = X0 ∨ (M.op X1 (τ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e3337 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e3337
          | (have j0 := b2e3337 X0 X1
             grind)
          | exact resolve b2e3337 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3337
        have b2e3723 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x x))) ∨ (τ X0) = (M.op x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 (M.op x x)
             have i₂ := b2e55 (τ X0)
             grind)
          | exact superpose b2e55 b2e24
          | (have j1 := b2e55 (τ X0)
             grind)
          | exact resolve b2e24 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e3730 : ∀ X0 : G, (k X0 (σ (M.op x x))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e3723 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e3723
          | (have j0 := b2e3723 X0
             grind)
          | exact resolve b2e3723 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3723
        have b2e4545 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b2e49 X0 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e4546 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e4545 X0
             have i₂ := b2e12 (M.op X0 (M.op X0 X0)) X0 (M.op X0 X0)
             grind)
          | exact superpose b2e12 b2e4545
          | exact resolve b2e4545 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4545
        have b2e4619 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b2e4546 X0
             have i₂ := b2e12 (M.op X0 X0) X0 (M.op X0 X0)
             grind)
          | exact superpose b2e12 b2e4546
          | exact resolve b2e4546 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4546
        have b2e4685 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op x X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e4619 X0
             have i₂ := b2e205 X0 X0
             grind)
          | exact superpose b2e205 b2e4619
          | exact resolve b2e4619 b2e205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e205 b2e4619
        have b2e4742 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (k (M.op x X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e4685 X0
             have i₂ := b2e179 X0 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e179 b2e4685
          | exact resolve b2e4685 b2e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4685
        have b2e4795 : ∀ X0 : G, (M.op x x) = (k (M.op x X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e4742 X0
             have i₂ := b2e219 X0 X0
             grind)
          | exact superpose b2e219 b2e4742
          | exact resolve b2e4742 b2e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4742
        have b2e4882 : ∀ X0 X1 : G, (M.op x x) = (k (M.op x x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e4795 (M.op X0 X1)
             have i₂ := b2e219 X0 X1
             grind)
          | exact superpose b2e219 b2e4795
          | exact resolve b2e4795 b2e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4906 : ∀ X0 : G, (σ (M.op x x)) = (k (σ (M.op x (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 (M.op x (τ X0))
             have i₂ := b2e4795 (τ X0)
             grind)
          | exact superpose b2e4795 b2e25
          | exact resolve b2e25 b2e4795
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5488 : (σ (M.op x x)) = (M.op (σ (M.op x (τ (σ y)))) (σ y)) ∨ (σ (M.op x (τ (σ y)))) = (M.op (σ (M.op x (τ (σ y)))) (σ y)) := by
          first
          | (have i₁ := b2e94 (σ (M.op x (τ (σ y))))
             have i₂ := b2e4906 (σ y)
             grind)
          | exact superpose b2e4906 b2e94
          | (have j0 := b2e94 (σ (M.op x (τ (σ y))))
             grind)
          | exact resolve b2e94 b2e4906
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5489 : ∀ X0 : G, (k (σ (σ (M.op x (τ (τ X0))))) X0) = (σ (σ (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 (σ (M.op x (τ (τ X0))))
             have i₂ := b2e4906 (τ X0)
             grind)
          | exact superpose b2e4906 b2e25
          | exact resolve b2e25 b2e4906
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4906
        have b2e5490 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x (τ (σ y)))) = (M.op (σ (M.op x (τ (σ y)))) (σ y)) := by
          first
          | (have i₁ := b2e5488
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e5488
          | exact resolve b2e5488 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5488
        have b2e5501 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x (τ (σ y)))) = (M.op (σ (M.op x (τ (σ y)))) (σ y)) := by
          first
          | (have i₁ := b2e5490
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5490
          | exact resolve b2e5490 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5490
        have b2e5504 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e5501
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e5501
          | exact resolve b2e5501 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5501
        have b2e5507 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e5504
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5504
          | exact resolve b2e5504 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5504
        have b2e5509 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e5507
             have r₂ := b2e21
             grind)
          | exact resolve b2e5507 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5507
        have b2e5603 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e82 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5604 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e82 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e5605 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e5603 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5603
        have b2e5723 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e5509
             grind)
          | exact superpose b2e5509 b2e21
          | exact resolve b2e21 b2e5509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5744 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
          intro X0
          first
          | (have i₁ := b2e179 (σ x) (σ y) X0
             have i₂ := b2e5509
             grind)
          | exact superpose b2e5509 b2e179
          | exact resolve b2e179 b2e5509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5745 : (M.op x x) = (M.op x (σ (M.op x x))) := by
          first
          | (have i₁ := b2e219 (σ x) (σ y)
             have i₂ := b2e5509
             grind)
          | exact superpose b2e5509 b2e219
          | exact resolve b2e219 b2e5509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12551 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
          first
          | (have i₁ := b2e5605 (M.op x x)
             have i₂ := b2e4882 x x
             grind)
          | exact superpose b2e4882 b2e5605
          | (have j0 := b2e5605 (M.op x x)
             grind)
          | exact resolve b2e5605 b2e4882
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4882 b2e5605
        have b2e12556 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
        clear b2e12551
        have b2e12565 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
          first
          | (have i₁ := b2e12556
             have i₂ := b2e5744 (σ (M.op x x))
             grind)
          | exact superpose b2e5744 b2e12556
          | exact resolve b2e12556 b2e5744
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12556
        have b2e12573 : (M.op x x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e12565
             have i₂ := b2e5745
             grind)
          | exact superpose b2e5745 b2e12565
          | exact resolve b2e12565 b2e5745
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5745 b2e12565
        have b2e12593 : (σ x) ≠ (M.op x x) := by
          first
          | (have i₁ := b2e5723
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e5723
          | exact resolve b2e5723 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5723
        have b2e12594 : (M.op x x) = (τ (M.op x x)) := by
          first
          | (have i₁ := b2e13 (M.op x x)
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e13
          | exact resolve b2e13 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12595 : ∀ X0 : G, (k (M.op x x) (σ X0)) = (σ (k (M.op x x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 (M.op x x) X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e18
          | exact resolve b2e18 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12596 : ∀ X0 : G, (k (σ X0) (M.op x x)) = (σ (k X0 (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 (M.op x x)
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e18
          | exact resolve b2e18 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12609 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (k (M.op x x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e111 (M.op x x) X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e111
          | exact resolve b2e111 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12617 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x x) = (k (M.op x X0) y) := by
          intro X0
          first
          | (have i₁ := b2e418 y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e418
          | (have j0 := b2e418 y X0
             grind)
          | exact resolve b2e418 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e418
        have b2e14549 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (k X0 y)) X1) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e179 (σ X0) (σ y) X1
             have i₂ := b2e902 X0
             grind)
          | exact superpose b2e902 b2e179
          | (have j1 := b2e902 X0
             grind)
          | exact resolve b2e179 b2e902
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e902
        have b2e16141 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ (M.op X0 (τ (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e94 (σ y)
             have i₂ := b2e3346 (σ y) X0
             grind)
          | exact superpose b2e3346 b2e94
          | (have j0 := b2e94 (σ y)
             have j1 := b2e3346 (σ y) X0
             grind)
          | exact resolve b2e94 b2e3346
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94 b2e3346
        have b2e16149 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ (M.op X0 (τ (σ y))) = X0 := by
          intro X0
          first
          | (have j0 := b2e16141 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16141
        have b2e16182 : ∀ X0 : G, (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ (M.op X0 (τ (σ y))) = X0 := by
          intro X0
          first
          | (have j0 := b2e16149 X0
             grind)
          | (have r₁ := b2e16149 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e16149 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16149
        have b2e16203 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (M.op X0 (τ (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16182 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e16182
          | (have j0 := b2e16182 X0
             grind)
          | exact resolve b2e16182 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16182
        have b2e16215 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16203 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e16203
          | (have j0 := b2e16203 X0
             grind)
          | exact resolve b2e16203 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16203
        have b2e16247 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 y
             have i₂ := b2e16215 (τ X0)
             grind)
          | exact superpose b2e16215 b2e24
          | (have j1 := b2e16215 (τ X0)
             grind)
          | exact resolve b2e24 b2e16215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e16755 : (k (M.op x x) (τ y)) = (τ (M.op (M.op x x) y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e12609 y
             have i₂ := b2e16215 (M.op x x)
             grind)
          | exact superpose b2e16215 b2e12609
          | (have j1 := b2e16215 (M.op x x)
             grind)
          | exact resolve b2e12609 b2e16215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12609 b2e16215
        have b2e16772 : (k (M.op x x) (τ y)) = (τ (M.op y (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e16755
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e16755
          | exact resolve b2e16755 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16755
        have b2e16792 : (k (M.op x x) (τ y)) = (τ (M.op x y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e16772
             have i₂ := b2e34 y
             grind)
          | exact superpose b2e34 b2e16772
          | exact resolve b2e16772 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16772
        have b2e16805 : (τ x) = (k (M.op x x) (τ y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e16792
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16792
          | exact resolve b2e16792 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16792
        have b2e16810 : (M.op x x) = (M.op y (M.op x x)) ∨ (τ x) = (k (M.op x x) (τ y)) := by
          first
          | (have i₁ := b2e16805
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e16805
          | exact resolve b2e16805 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16805
        have b2e16812 : (M.op x y) = (M.op x x) ∨ (τ x) = (k (M.op x x) (τ y)) := by
          first
          | (have i₁ := b2e16810
             have i₂ := b2e34 y
             grind)
          | exact superpose b2e34 b2e16810
          | exact resolve b2e16810 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16810
        have b2e16814 : (τ x) = (k (M.op x x) (τ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e16812
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16812
          | exact resolve b2e16812 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16812
        have b2e21439 : (k (σ (M.op x x)) y) = (σ (τ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e25 y (M.op x x)
             have i₂ := b2e16814
             grind)
          | exact superpose b2e16814 b2e25
          | exact resolve b2e25 b2e16814
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16814
        have b2e21460 : x = (k (σ (M.op x x)) y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e21439
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e21439
          | exact resolve b2e21439 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21439
        have b2e21482 : x = (k (M.op x x) y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e21460
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e21460
          | exact resolve b2e21460 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21460
        have b2e21581 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e5604 (τ X0) (τ X1)
             have i₂ := b2e114 X1 X0
             grind)
          | exact superpose b2e114 b2e5604
          | (have j0 := b2e5604 (τ X1) (τ X1)
             grind)
          | exact resolve b2e5604 b2e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e114 b2e5604
        have b2e21622 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e21581 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e21581
          | (have j0 := b2e21581 X1 X1
             grind)
          | exact resolve b2e21581 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21581
        have b2e21653 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e21622 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e21622
          | (have j0 := b2e21622 X1 X1
             grind)
          | exact resolve b2e21622 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21622
        have b2e21676 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e21653 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e21653
          | (have j0 := b2e21653 X0 X1
             grind)
          | exact resolve b2e21653 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21653
        have b2e21691 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e21676 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e21676
          | (have j0 := b2e21676 X0 X1
             grind)
          | exact resolve b2e21676 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21676
        have b2e21702 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e21691 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e21691
          | (have j0 := b2e21691 X0 X1
             grind)
          | exact resolve b2e21691 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21691
        have b2e26191 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op x x)))) ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 (σ (M.op x x))
             have i₂ := b2e3730 (τ X0)
             grind)
          | exact superpose b2e3730 b2e24
          | (have j1 := b2e3730 (τ X0)
             grind)
          | exact resolve b2e24 b2e3730
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3730
        have b2e26228 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x x))) ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e26191 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e26191
          | (have j0 := b2e26191 X0
             grind)
          | exact resolve b2e26191 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26191
        have b2e26277 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op x x)) ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e26228 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e26228
          | (have j0 := b2e26228 X0
             grind)
          | exact resolve b2e26228 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26228
        have b2e26313 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e26277 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26277
          | (have j0 := b2e26277 X0
             grind)
          | exact resolve b2e26277 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26277
        have b2e32685 : ∀ X0 : G, (σ (σ (σ (M.op x x)))) = (k (σ (σ (σ (M.op x (τ (τ (τ X0))))))) X0) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 (σ (σ (M.op x (τ (τ (τ X0))))))
             have i₂ := b2e5489 (τ X0)
             grind)
          | exact superpose b2e5489 b2e25
          | exact resolve b2e25 b2e5489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e5489
        have b2e32696 : ∀ X0 : G, (σ (σ (M.op x x))) = (k (σ (σ (σ (M.op x (τ (τ (τ X0))))))) X0) := by
          intro X0
          first
          | (have i₁ := b2e32685 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e32685
          | exact resolve b2e32685 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32685
        have b2e32794 : ∀ X0 : G, (σ (M.op x x)) = (k (σ (σ (σ (M.op x (τ (τ (τ X0))))))) X0) := by
          intro X0
          first
          | (have i₁ := b2e32696 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e32696
          | exact resolve b2e32696 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32696
        have b2e32879 : ∀ X0 : G, (M.op x x) = (k (σ (σ (σ (M.op x (τ (τ (τ X0))))))) X0) := by
          intro X0
          first
          | (have i₁ := b2e32794 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e32794
          | exact resolve b2e32794 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32794
        have b2e46308 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x x))) ∨ (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 (M.op x x)
             have i₂ := b2e26313 (τ X0)
             grind)
          | exact superpose b2e26313 b2e24
          | (have j1 := b2e26313 (τ X0)
             grind)
          | exact resolve b2e24 b2e26313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e26313
        have b2e46368 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op x x)) ∨ (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e46308 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e46308
          | (have j0 := b2e46308 X0
             grind)
          | exact resolve b2e46308 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46308
        have b2e46428 : ∀ X0 : G, (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e46368 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e46368
          | (have j0 := b2e46368 X0
             grind)
          | exact resolve b2e46368 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46368
        have b2e75058 : (k (M.op x x) (σ y)) = (σ (M.op (M.op x x) y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e16247 (M.op x x)
             have i₂ := b2e12594
             grind)
          | exact superpose b2e12594 b2e16247
          | exact resolve b2e16247 b2e12594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16247
        have b2e75166 : (k (M.op x x) (σ y)) = (σ (M.op y (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e75058
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e75058
          | exact resolve b2e75058 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75058
        have b2e75172 : (σ (M.op x y)) = (k (M.op x x) (σ y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e75166
             have i₂ := b2e34 y
             grind)
          | exact superpose b2e34 b2e75166
          | exact resolve b2e75166 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75166
        have b2e75173 : (σ (M.op x y)) = (σ (k (M.op x x) y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e75172
             have i₂ := b2e12595 y
             grind)
          | exact superpose b2e12595 b2e75172
          | exact resolve b2e75172 b2e12595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75172
        have b2e75174 : (σ x) = (σ (k (M.op x x) y)) ∨ (M.op x x) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e75173
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e75173
          | exact resolve b2e75173 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75173
        have b2e75175 : (M.op x x) = (M.op y (M.op x x)) ∨ (σ x) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b2e75174
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e75174
          | exact resolve b2e75174 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75174
        have b2e75176 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b2e75175
             have i₂ := b2e34 y
             grind)
          | exact superpose b2e34 b2e75175
          | exact resolve b2e75175 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e75175
        have b2e75177 : (σ x) = (σ (k (M.op x x) y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e75176
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e75176
          | exact resolve b2e75176 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75176
        have b2e76635 : ∀ X0 : G, (k (k (M.op x x) y) (τ X0)) = (τ (k (σ x) X0)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e111 (k (M.op x x) y) X0
             have i₂ := b2e75177
             grind)
          | exact superpose b2e75177 b2e111
          | exact resolve b2e111 b2e75177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75177
        have b2e76724 : ∀ X0 : G, (k x (τ X0)) = (k (k (M.op x x) y) (τ X0)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e76635 X0
             have i₂ := b2e111 x X0
             grind)
          | exact superpose b2e111 b2e76635
          | exact resolve b2e76635 b2e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76635
        have b2e104214 : ∀ X0 : G, (M.op x x) = (k (σ (σ (σ (τ (τ (τ X0)))))) X0) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32879 X0
             have i₂ := b2e46428 X0
             grind)
          | exact superpose b2e46428 b2e32879
          | (have j1 := b2e46428 X0
             grind)
          | exact resolve b2e32879 b2e46428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32879
        have b2e104263 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (τ (τ X0))) X1) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e179 x (τ (τ (τ X0))) X1
             have i₂ := b2e46428 X0
             grind)
          | exact superpose b2e46428 b2e179
          | (have j1 := b2e46428 X0
             grind)
          | exact resolve b2e179 b2e46428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e179
        have b2e104265 : ∀ X0 : G, (M.op x x) = (M.op x (τ (τ (τ X0)))) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e219 x (τ (τ (τ X0)))
             have i₂ := b2e46428 X0
             grind)
          | exact superpose b2e46428 b2e219
          | (have j1 := b2e46428 X0
             grind)
          | exact resolve b2e219 b2e46428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e104316 : ∀ X0 : G, (M.op x x) = (k (σ (σ (τ (τ X0)))) X0) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e104214 X0
             have i₂ := b2e14 (τ (τ X0))
             grind)
          | exact superpose b2e14 b2e104214
          | (have j0 := b2e104214 X0
             grind)
          | exact resolve b2e104214 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104214
        have b2e104334 : ∀ X0 : G, (M.op x x) = (k (σ (τ X0)) X0) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e104316 X0
             have i₂ := b2e14 (τ X0)
             grind)
          | exact superpose b2e14 b2e104316
          | (have j0 := b2e104316 X0
             grind)
          | exact resolve b2e104316 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104316
        have b2e104344 : ∀ X0 : G, (M.op x x) = (k X0 X0) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e104334 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e104334
          | (have j0 := b2e104334 X0
             grind)
          | exact resolve b2e104334 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104334
        have b2e104470 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21702 X0 X0
             have i₂ := b2e104344 X0
             grind)
          | exact superpose b2e104344 b2e21702
          | (have j0 := b2e21702 X0 X0
             have j1 := b2e104344 X0
             grind)
          | (have r₁ := b2e21702 (M.op x x) (M.op x x)
             have r₂ := b2e104344 (M.op x x)
             grind)
          | (have r₁ := b2e21702 X0 (M.op x x)
             have r₂ := b2e104344 X0
             grind)
          | exact resolve b2e21702 b2e104344
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21702 b2e104344
        have b2e104580 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e104470 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104470
        have b2e107747 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (τ X0)) X1) ∨ (σ X0) = (k (σ X0) (M.op x x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e104263 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e104263
          | (have j0 := b2e104263 (σ X0) X1
             grind)
          | exact resolve b2e104263 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104263
        have b2e107930 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op x x))) ∨ (M.op x X1) = (M.op (τ (τ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e107747 X0 X1
             have i₂ := b2e12596 X0
             grind)
          | exact superpose b2e12596 b2e107747
          | (have j0 := b2e107747 X0 X1
             grind)
          | exact resolve b2e107747 b2e12596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12596 b2e107747
        have b2e108173 : ∀ X0 : G, (M.op x x) = (τ (τ (τ X0))) ∨ (k X0 (M.op x x)) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e46428 X0
             have i₂ := b2e104265 X0
             grind)
          | exact superpose b2e104265 b2e46428
          | (have j0 := b2e46428 X0
             have j1 := b2e104265 X0
             grind)
          | exact resolve b2e46428 b2e104265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46428 b2e104265
        have b2e108252 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x x) = (τ (τ (τ X0))) := by
          intro X0
          first
          | (have j0 := b2e108173 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108173
        have b2e108364 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x x))) ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e111 X0 (M.op x x)
             have i₂ := b2e108252 (σ X0)
             grind)
          | exact superpose b2e108252 b2e111
          | (have j1 := b2e108252 (σ X0)
             grind)
          | exact resolve b2e111 b2e108252
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108252
        have b2e108425 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op x x)) ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e108364 X0
             have i₂ := b2e12594
             grind)
          | exact superpose b2e12594 b2e108364
          | (have j0 := b2e108364 X0
             grind)
          | exact resolve b2e108364 b2e12594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108364
        have b2e108463 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e108425 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e108425
          | (have j0 := b2e108425 X0
             grind)
          | exact resolve b2e108425 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108425
        have b2e108486 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x x) = (τ (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e108463 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e108463
          | (have j0 := b2e108463 X0
             grind)
          | exact resolve b2e108463 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108463
        have b2e108579 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x x))) ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e111 X0 (M.op x x)
             have i₂ := b2e108486 (σ X0)
             grind)
          | exact superpose b2e108486 b2e111
          | (have j1 := b2e108486 (σ X0)
             grind)
          | exact resolve b2e111 b2e108486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108486
        have b2e108653 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op x x)) ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e108579 X0
             have i₂ := b2e12594
             grind)
          | exact superpose b2e12594 b2e108579
          | (have j0 := b2e108579 X0
             grind)
          | exact resolve b2e108579 b2e12594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108579
        have b2e108696 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e108653 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e108653
          | (have j0 := b2e108653 X0
             grind)
          | exact resolve b2e108653 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108653
        have b2e108720 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (τ X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e108696 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e108696
          | (have j0 := b2e108696 X0
             grind)
          | exact resolve b2e108696 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108696
        have b2e108856 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x x))) ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e111 X0 (M.op x x)
             have i₂ := b2e108720 (σ X0)
             grind)
          | exact superpose b2e108720 b2e111
          | (have j1 := b2e108720 (σ X0)
             grind)
          | exact resolve b2e111 b2e108720
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108720
        have b2e108930 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op x x)) ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e108856 X0
             have i₂ := b2e12594
             grind)
          | exact superpose b2e12594 b2e108856
          | (have j0 := b2e108856 X0
             grind)
          | exact resolve b2e108856 b2e12594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108856
        have b2e108970 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e108930 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e108930
          | (have j0 := b2e108930 X0
             grind)
          | exact resolve b2e108930 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108930
        have b2e108994 : ∀ X0 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e108970 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e108970
          | (have j0 := b2e108970 X0
             grind)
          | exact resolve b2e108970 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108970
        have b2e126471 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op x x)) ∨ (M.op x X1) = (M.op (τ (τ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (M.op x x))
             have i₂ := b2e107930 X0 X1
             grind)
          | exact superpose b2e107930 b2e13
          | (have j1 := b2e107930 X0 X1
             grind)
          | exact resolve b2e13 b2e107930
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107930
        have b2e126620 : ∀ X0 X1 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x X1) = (M.op (τ (τ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e126471 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e126471
          | (have j0 := b2e126471 X0 X1
             grind)
          | exact resolve b2e126471 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126471
        have b2e126747 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op x x))) ∨ (M.op x X1) = (M.op (τ (τ (σ X0))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e111 X0 (M.op x x)
             have i₂ := b2e126620 (σ X0) X1
             grind)
          | exact superpose b2e126620 b2e111
          | (have j1 := b2e126620 (σ X0) X1
             grind)
          | exact resolve b2e111 b2e126620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126620
        have b2e126930 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op x x)) ∨ (M.op x X1) = (M.op (τ (τ (σ X0))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e126747 X0 X1
             have i₂ := b2e12594
             grind)
          | exact superpose b2e12594 b2e126747
          | (have j0 := b2e126747 X0 X1
             grind)
          | exact resolve b2e126747 b2e12594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126747
        have b2e126996 : ∀ X0 X1 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x X1) = (M.op (τ (τ (σ X0))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e126930 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e126930
          | (have j0 := b2e126930 X0 X1
             grind)
          | exact resolve b2e126930 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126930
        have b2e127027 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ X0) X1) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e126996 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e126996
          | (have j0 := b2e126996 X0 X1
             grind)
          | exact resolve b2e126996 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126996
        have b2e127187 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op x x))) ∨ (M.op x X1) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e111 X0 (M.op x x)
             have i₂ := b2e127027 (σ X0) X1
             grind)
          | exact superpose b2e127027 b2e111
          | (have j1 := b2e127027 (σ X0) X1
             grind)
          | exact resolve b2e111 b2e127027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e111 b2e127027
        have b2e127242 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op x x)) ∨ (M.op x X1) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e127187 X0 X1
             have i₂ := b2e12594
             grind)
          | exact superpose b2e12594 b2e127187
          | (have j0 := b2e127187 X0 X1
             grind)
          | exact resolve b2e127187 b2e12594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12594 b2e127187
        have b2e127333 : ∀ X0 X1 : G, (k X0 (M.op x x)) = X0 ∨ (M.op x X1) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e127242 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e127242
          | (have j0 := b2e127242 X0 X1
             grind)
          | exact resolve b2e127242 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127242
        have b2e127384 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e127333 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e127333
          | (have j0 := b2e127333 X0 X1
             grind)
          | exact resolve b2e127333 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127333
        have b2e127698 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op X0 (M.op X1 X2)) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e219 X1 X2
             have i₂ := b2e127384 X0 (M.op X1 X2)
             grind)
          | (have i₁ := b2e219 X0 X1
             have i₂ := b2e127384 x (M.op X0 X1)
             grind)
          | exact superpose b2e127384 b2e219
          | (have j1 := b2e127384 X0 X1
             grind)
          | exact resolve b2e219 b2e127384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e219 b2e127384
        have b2e130736 : ∀ X0 X1 X2 : G, (M.op x x) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 X2)) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 X2)
             have i₂ := b2e127698 X0 X1 X2
             grind)
          | exact superpose b2e127698 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X2)
             have j1 := b2e127698 X0 X1 X2
             grind)
          | (have r₁ := b2e15 (M.op x x) (M.op X1 X2)
             have r₂ := b2e127698 (M.op x x) X1 X2
             grind)
          | exact resolve b2e15 b2e127698
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127698
        have b2e130945 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 X2)) ∨ (k X0 (M.op x x)) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e130736 X0 X1 X2
             have j1 := b2e108994 X0
             grind)
          | (have r₁ := b2e130736 (k (M.op x x) (M.op x x)) X1 X2
             have r₂ := b2e108994 (M.op x x)
             grind)
          | (have r₁ := b2e130736 X0 X1 X2
             have r₂ := b2e108994 X0
             grind)
          | (have r₁ := b2e130736 (M.op x x) X1 X2
             have r₂ := b2e108994 (M.op x x)
             grind)
          | exact resolve b2e130736 b2e108994
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130736
        have b2e132382 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x x) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e108994 X0
             have i₂ := b2e130945 X0 x x
             grind)
          | exact superpose b2e130945 b2e108994
          | (have j0 := b2e108994 X0
             have j1 := b2e130945 X0 x x
             grind)
          | exact resolve b2e108994 b2e130945
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e132466 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e130945 X0 x x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130945
        have b2e132490 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e132382 X0
             have j1 := b2e104580 X0
             grind)
          | (have r₁ := b2e132382 x
             have r₂ := b2e104580 x
             grind)
          | (have r₁ := b2e132382 (M.op x x)
             have r₂ := b2e104580 (M.op (M.op x x) (M.op x x))
             grind)
          | (have r₁ := b2e132382 X0
             have r₂ := b2e104580 X0
             grind)
          | exact resolve b2e132382 b2e104580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104580 b2e132382
        have b2e132555 : ∀ X0 : G, (k X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have j0 := b2e132490 X0
             have j1 := b2e132466 X0
             grind)
          | (have r₁ := b2e132490 X0
             have r₂ := b2e132466 X0
             grind)
          | exact resolve b2e132490 b2e132466
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132466 b2e132490
        have b2e137782 : ∀ X0 : G, (k x X0) = (k (k (M.op x x) y) X0) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e76724 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e76724
          | exact resolve b2e76724 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76724
        have b2e137857 : (k x (M.op x x)) = (k (M.op x x) y) ∨ (M.op x x) = (k (M.op x x) y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e108994 (k (M.op x x) y)
             have i₂ := b2e137782 (M.op x x)
             grind)
          | exact superpose b2e137782 b2e108994
          | (have j0 := b2e108994 (k (M.op x x) y)
             grind)
          | exact resolve b2e108994 b2e137782
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108994 b2e137782
        have b2e137923 : (k x (M.op x x)) = (k (M.op x x) y) ∨ (M.op x x) = (k (M.op x x) y) := by
          first
          | (have j1 := b2e12617 x
             grind)
          | (have r₁ := b2e137857
             have r₂ := b2e12617 x
             grind)
          | exact resolve b2e137857 b2e12617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12617 b2e137857
        have b2e137961 : (M.op x x) = (k (M.op x x) y) ∨ x = (k (M.op x x) y) := by
          first
          | (have i₁ := b2e137923
             have i₂ := b2e132555 x
             grind)
          | exact superpose b2e132555 b2e137923
          | exact resolve b2e137923 b2e132555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132555 b2e137923
        have b2e137992 : x ≠ (M.op x x) ∨ x = (k (M.op x x) y) := by grind
        clear b2e137961
        have b2e137996 : x = (k (M.op x x) y) := by
          first
          | (have r₁ := b2e137992
             have r₂ := b2e21482
             grind)
          | exact resolve b2e137992 b2e21482
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21482 b2e137992
        have b2e138040 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e14549 (M.op x x) X0
             have i₂ := b2e137996
             grind)
          | exact superpose b2e137996 b2e14549
          | (have j0 := b2e14549 (M.op x x) x
             grind)
          | exact resolve b2e14549 b2e137996
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14549
        have b2e138151 : ∀ X0 : G, (σ (M.op x x)) = (M.op x (σ y)) ∨ (M.op x X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e138040 X0
             have i₂ := b2e5744 (σ y)
             grind)
          | exact superpose b2e5744 b2e138040
          | (have j0 := b2e138040 X0
             grind)
          | exact resolve b2e138040 b2e5744
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5744 b2e138040
        have b2e138217 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) ∨ (M.op x x) = (M.op x (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e138151 X0
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e138151
          | (have j0 := b2e138151 X0
             grind)
          | exact resolve b2e138151 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138151
        have b2e141009 : (σ (M.op x x)) = (M.op x (σ y)) ∨ (M.op x x) = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e5509
             have i₂ := b2e138217 (σ y)
             grind)
          | exact superpose b2e138217 b2e5509
          | exact resolve b2e5509 b2e138217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5509 b2e138217
        have b2e141162 : (M.op x x) = (M.op x (σ y)) ∨ (M.op x x) = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e141009
             have i₂ := b2e12573
             grind)
          | exact superpose b2e12573 b2e141009
          | exact resolve b2e141009 b2e12573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12573 b2e141009
        have b2e141163 : (M.op x x) = (M.op x (σ y)) := by grind
        clear b2e141162
        have b2e141239 : (M.op x x) = (k (M.op x x) (σ y)) := by
          first
          | (have i₁ := b2e4795 (σ y)
             have i₂ := b2e141163
             grind)
          | exact superpose b2e141163 b2e4795
          | exact resolve b2e4795 b2e141163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4795 b2e141163
        have b2e141362 : (M.op x x) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b2e141239
             have i₂ := b2e12595 y
             grind)
          | exact superpose b2e12595 b2e141239
          | exact resolve b2e141239 b2e12595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12595 b2e141239
        have b2e141373 : (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e141362
             have i₂ := b2e137996
             grind)
          | exact superpose b2e137996 b2e141362
          | exact resolve b2e141362 b2e137996
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137996 b2e141362
        have b2e141376 : False := by grind
        exact b2e141376
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 X0 X3
             have i₂ := b3e12 X2 X0 X1
             grind)
          | (have i₁ := b3e12 (M.op X1 X2) X1 X2
             have i₂ := b3e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
        have b3e41 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op X1 (M.op y y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 y X0
             have i₂ := b3e34 X0
             grind)
          | (have i₁ := b3e12 X0 X0 y
             have i₂ := b3e34 X0
             grind)
          | exact superpose b3e34 b3e12
          | exact resolve b3e12 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e41 X0 X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e41
          | exact resolve b3e41 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e47 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e47
        have b3e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e51
          | exact resolve b3e51 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e57 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 : G, (k X0 y) = X0 ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e251 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 (σ x) X0 X1 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e29
          | exact resolve b3e29 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e277 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op y (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e34 (M.op X0 X2)
             have i₂ := b3e29 X0 X2 y X1
             grind)
          | (have i₁ := b3e34 (M.op X0 X2)
             have i₂ := b3e29 X0 X1 y X2
             grind)
          | exact superpose b3e29 b3e34
          | exact resolve b3e34 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e282 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e42 X0 X2
             have i₂ := b3e29 X0 y X2 X1
             grind)
          | (have i₁ := b3e42 X0 X2
             have i₂ := b3e29 X0 X1 X2 y
             grind)
          | exact superpose b3e29 b3e42
          | exact resolve b3e42 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e297 : ∀ X0 X2 : G, (M.op y y) = (M.op y (M.op X0 X2)) := by
          intro X0 X2
          first
          | (have i₁ := b3e277 X0 x X2
             have i₂ := b3e282 X0 x y
             grind)
          | exact superpose b3e282 b3e277
          | exact resolve b3e277 b3e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e277
        have b3e311 : ∀ X1 : G, (M.op X1 y) = (M.op (σ x) X1) := by
          intro X1
          first
          | (have i₁ := b3e251 x X1
             have i₂ := b3e282 (σ x) x X1
             grind)
          | exact superpose b3e282 b3e251
          | exact resolve b3e251 b3e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e251
        have b3e341 : ∀ X0 X2 : G, y = (M.op y (M.op X0 X2)) := by
          intro X0 X2
          first
          | (have i₁ := b3e297 X0 X2
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e297
          | exact resolve b3e297 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e297
        have b3e389 : ∀ X0 X1 : G, y ≠ y ∨ (M.op y y) = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 y (M.op X0 X1)
             have i₂ := b3e341 X0 X1
             grind)
          | exact superpose b3e341 b3e15
          | (have j0 := b3e15 y (M.op X0 X1)
             grind)
          | (have r₁ := b3e15 y (M.op X0 x)
             have r₂ := b3e341 X0 x
             grind)
          | exact resolve b3e15 b3e341
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341
        have b3e391 : ∀ X0 X1 : G, (M.op y y) = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e389 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e389
        have b3e393 : ∀ X0 X1 : G, y = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e391 X0 X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e391
          | exact resolve b3e391 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e391
        have b3e1224 : y = (k y (σ (k x y))) := by
          first
          | (have i₁ := b3e393 (σ x) (σ x)
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e393
          | exact resolve b3e393 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e393
        have b3e1347 : (σ (k x y)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e311 (σ x)
             grind)
          | exact superpose b3e311 b3e53
          | exact resolve b3e53 b3e311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e1353 : (M.op y y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e1347
             have i₂ := b3e311 y
             grind)
          | (have i₁ := b3e1347
             have i₂ := b3e311 (σ x)
             grind)
          | exact superpose b3e311 b3e1347
          | exact resolve b3e1347 b3e311
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e311 b3e1347
        have b3e1378 : y = (σ (k x y)) := by
          first
          | (have i₁ := b3e1353
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1353
          | exact resolve b3e1353 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1353
        have b3e1935 : y = (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e1378
             have i₂ := b3e58 x
             grind)
          | exact superpose b3e58 b3e1378
          | (have j1 := b3e58 x
             grind)
          | exact resolve b3e1378 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e1939 : (k x y) = (τ y) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e1378
             grind)
          | exact superpose b3e1378 b3e13
          | exact resolve b3e13 b3e1378
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1378
        have b3e1942 : y = (σ x) := by
          first
          | (have r₁ := b3e1935
             have r₂ := b3e20
             grind)
          | exact resolve b3e1935 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1935
        have b3e2578 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e1942
             grind)
          | exact superpose b3e1942 b3e18
          | exact resolve b3e18 b3e1942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2579 : ∀ X0 : G, (k y (σ X0)) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e1942
             grind)
          | exact superpose b3e1942 b3e18
          | exact resolve b3e18 b3e1942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2580 : x = (τ y) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e1942
             grind)
          | exact superpose b3e1942 b3e13
          | exact resolve b3e13 b3e1942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1942
        have b3e4662 : y = (k y (σ (τ y))) := by
          first
          | (have i₁ := b3e1224
             have i₂ := b3e1939
             grind)
          | exact superpose b3e1939 b3e1224
          | exact resolve b3e1224 b3e1939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1224 b3e1939
        have b3e4678 : y = (σ (k x (τ y))) := by
          first
          | (have i₁ := b3e4662
             have i₂ := b3e2579 (τ y)
             grind)
          | exact superpose b3e2579 b3e4662
          | exact resolve b3e4662 b3e2579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2579 b3e4662
        have b3e4679 : y = (k (σ x) y) := by
          first
          | (have i₁ := b3e4678
             have i₂ := b3e25 y x
             grind)
          | exact superpose b3e25 b3e4678
          | exact resolve b3e4678 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e4678
        have b3e4680 : y = (σ (k x x)) := by
          first
          | (have i₁ := b3e4679
             have i₂ := b3e2578 x
             grind)
          | exact superpose b3e2578 b3e4679
          | exact resolve b3e4679 b3e2578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2578 b3e4679
        have b3e5226 : (k x x) = (τ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e4680
             grind)
          | exact superpose b3e4680 b3e13
          | exact resolve b3e13 b3e4680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4680
        have b3e5228 : x = (k x x) := by
          first
          | (have i₁ := b3e5226
             have i₂ := b3e2580
             grind)
          | exact superpose b3e2580 b3e5226
          | exact resolve b3e5226 b3e2580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2580 b3e5226
        have b3e5452 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e5228
             grind)
          | exact superpose b3e5228 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e5228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5228
        have b3e5453 : x = (M.op x x) := by grind
        clear b3e5452
        have b3e5547 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 x X0 X1 x
             have i₂ := b3e5453
             grind)
          | exact superpose b3e5453 b3e29
          | exact resolve b3e29 b3e5453
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e5569 : ∀ X1 : G, (M.op X1 y) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b3e5547 x X1
             have i₂ := b3e282 x x X1
             grind)
          | exact superpose b3e282 b3e5547
          | exact resolve b3e5547 b3e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e282 b3e5547
        have b3e6697 : x = (M.op x y) := by
          first
          | (have i₁ := b3e5453
             have i₂ := b3e5569 x
             grind)
          | exact superpose b3e5569 b3e5453
          | exact resolve b3e5453 b3e5569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5453 b3e5569
        have b3e6711 : False := by grind
        exact b3e6711
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b4e33 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X0 X3
               have i₂ := b4e13 X2 X0 X1
               grind)
            | (have i₁ := b4e13 (M.op X1 X2) X1 X2
               have i₂ := b4e13 (M.op X1 X1) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
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
          have b4e40 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
          have b4e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X0 X0) X2 X3
               have i₂ := b4e13 (M.op X2 X3) X0 X1
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 y
               have i₂ := b4e40 X0
               grind)
            | (have i₁ := b4e13 X0 y X0
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e48 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e44 X0 X1
               have i₂ := b4e34 X1 X0
               grind)
            | exact superpose b4e34 b4e44
            | exact resolve b4e44 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 (M.op X1 X2) X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | (have i₁ := b4e16 X0 (M.op X1 X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X1 X2) X0
               grind)
            | (have r₁ := b4e16 (M.op X0 (M.op X0 X0)) X0
               have r₂ := b4e13 X0 X0 (M.op X0 X0)
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op y y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e40 X0
               grind)
            | (have i₁ := b4e16 X0 y
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | exact resolve b4e16 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e54 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e54
            | (have j0 := b4e54 X0
               grind)
            | (have r₁ := b4e54 y
               have r₂ := b4e22
               grind)
            | exact resolve b4e54 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e59 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 y) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e51 X0 X1 X2
               have i₂ := b4e48 X1 X0
               grind)
            | exact superpose b4e48 b4e51
            | (have j0 := b4e51 X0 X1 X2
               grind)
            | (have r₁ := b4e51 X1 X1 y
               have r₂ := b4e48 X1 X1
               grind)
            | exact resolve b4e51 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X0 X1
               have i₂ := b4e18 (τ X0) X1
               grind)
            | exact superpose b4e18 b4e25
            | (have j1 := b4e18 X1 X1
               grind)
            | exact resolve b4e25 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e135 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e39 (σ x)
               grind)
            | exact superpose b4e39 b4e20
            | exact resolve b4e20 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e140 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X0 X1
               have i₂ := b4e39 (M.op X0 X1)
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e145 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e140 X0 X1
               have i₂ := b4e48 X0 (σ y)
               grind)
            | exact superpose b4e48 b4e140
            | exact resolve b4e140 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e140
          have b4e148 : (M.op (σ y) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e135
               have i₂ := b4e40 x
               grind)
            | exact superpose b4e40 b4e135
            | exact resolve b4e135 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e151 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op y (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e145 X0 X1
               have i₂ := b4e39 y
               grind)
            | exact superpose b4e39 b4e145
            | exact resolve b4e145 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145
          have b4e212 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) x
               have i₂ := b4e33 X0 x
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e214 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e39 (M.op (σ y) X0)
               have i₂ := b4e33 (σ y) X0
               grind)
            | exact superpose b4e33 b4e39
            | exact resolve b4e39 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e39
          have b4e217 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e214 x
               have i₂ := b4e151 (σ y) x
               grind)
            | exact superpose b4e151 b4e214
            | exact resolve b4e214 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151 b4e214
          have b4e219 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e212 X0
               have i₂ := b4e48 (σ y) X0
               grind)
            | exact superpose b4e48 b4e212
            | exact resolve b4e212 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e212
          have b4e232 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e217
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e217
            | exact resolve b4e217 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e217
          have b4e242 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b4e232
               have i₂ := b4e219 y
               grind)
            | exact superpose b4e219 b4e232
            | exact resolve b4e232 b4e219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e219 b4e232
          have b4e248 : y = (σ y) := by
            first
            | (have i₁ := b4e242
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e242
            | exact resolve b4e242 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242
          have b4e259 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e248
               grind)
            | exact superpose b4e248 b4e20
            | exact resolve b4e20 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e263 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e248
               grind)
            | exact superpose b4e248 b4e19
            | exact resolve b4e19 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e264 : y = (τ y) := by
            first
            | (have i₁ := b4e14 y
               have i₂ := b4e248
               grind)
            | exact superpose b4e248 b4e14
            | exact resolve b4e14 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e266 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e259
               have i₂ := b4e40 (σ x)
               grind)
            | exact superpose b4e40 b4e259
            | exact resolve b4e259 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e259
          have b4e267 : (σ (M.op y x)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e266
               have i₂ := b4e40 x
               grind)
            | exact superpose b4e40 b4e266
            | exact resolve b4e266 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e266
          have b4e295 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X0 X1 X2 y
               have i₂ := b4e40 X0
               grind)
            | (have i₁ := b4e35 y X1 X2 X0
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e35
            | exact resolve b4e35 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e336 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X2 X4) (M.op X0 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 (M.op X0 X3) X2 X4
               have i₂ := b4e35 X0 X3 (M.op X2 X2) X1
               grind)
            | (have i₁ := b4e13 (M.op X0 X3) X2 X4
               have i₂ := b4e35 X0 X1 (M.op X2 X2) X3
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e342 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X2 X4) (M.op X0 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e336 X0 X1 X2 X3 X4
               have i₂ := b4e48 X2 (M.op X0 X1)
               grind)
            | exact superpose b4e48 b4e336
            | exact resolve b4e336 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e336
          have b4e357 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e295 X0 X1 X2
               have i₂ := b4e34 X2 X0
               grind)
            | exact superpose b4e34 b4e295
            | exact resolve b4e295 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e295
          have b4e371 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X2 X4) (M.op X0 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e342 X0 X1 X2 X3 X4
               have i₂ := b4e40 (M.op X0 X1)
               grind)
            | exact superpose b4e40 b4e342
            | exact resolve b4e342 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342
          have b4e386 : ∀ X0 X1 X3 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X3) y) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e371 X0 X1 x X3 x
               have i₂ := b4e357 x x (M.op X0 X3)
               grind)
            | exact superpose b4e357 b4e371
            | exact resolve b4e371 b4e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e371
          have b4e392 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e386 X0 X1 x
               have i₂ := b4e357 X0 x y
               grind)
            | exact superpose b4e357 b4e386
            | exact resolve b4e386 b4e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e386
          have b4e396 : ∀ X0 X1 : G, y = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e392 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e392
            | exact resolve b4e392 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392
          have b4e419 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ y = (M.op y X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e396 X0 X0
               have i₂ := b4e18 X1 X0
               grind)
            | exact superpose b4e18 b4e396
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e396 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e732 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X0 (M.op X2 X2)) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e41 X0 X1 X2 X3
               have i₂ := b4e18 X4 X0
               grind)
            | exact superpose b4e18 b4e41
            | (have j1 := b4e18 X4 X0
               grind)
            | exact resolve b4e41 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e867 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 y) = (M.op (M.op X0 X1) (M.op X2 X3)) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e732 X0 X1 X2 X3 X4
               have i₂ := b4e48 X2 X0
               grind)
            | exact superpose b4e48 b4e732
            | (have j0 := b4e732 X0 X1 X2 X3 X4
               grind)
            | exact resolve b4e732 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e732
          have b4e963 : ∀ X0 X2 X3 X4 : G, (M.op X0 y) = (M.op (M.op X2 X3) y) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b4e867 X0 x X2 X3 X4
               have i₂ := b4e357 X0 x (M.op X2 X3)
               grind)
            | exact superpose b4e357 b4e867
            | (have j0 := b4e867 X0 x X2 X3 X4
               grind)
            | exact resolve b4e867 b4e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e867
          have b4e1049 : ∀ X0 X4 : G, (M.op y y) = (M.op X0 y) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
            intro X0 X4
            first
            | (have i₁ := b4e963 X0 x x X4
               have i₂ := b4e357 x x y
               grind)
            | exact superpose b4e357 b4e963
            | (have j0 := b4e963 X0 x x X4
               grind)
            | exact resolve b4e963 b4e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e963
          have b4e1099 : ∀ X0 X4 : G, (M.op X4 X0) = (k X4 X0) ∨ y = (M.op X0 y) ∨ (M.op X4 X0) = X4 := by
            intro X0 X4
            first
            | (have i₁ := b4e1049 X0 X4
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1049
            | (have j0 := b4e1049 X0 X4
               grind)
            | exact resolve b4e1049 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1049
          have b4e4031 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have j0 := b4e59 X0 X0 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e4032 : ∀ X0 : G, (M.op (M.op X0 y) y) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b4e4031 X0
               have i₂ := b4e357 X0 y (M.op X0 y)
               grind)
            | exact superpose b4e357 b4e4031
            | exact resolve b4e4031 b4e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4031
          have b4e4053 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b4e4032 X0
               have i₂ := b4e357 X0 y y
               grind)
            | exact superpose b4e357 b4e4032
            | exact resolve b4e4032 b4e357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e357 b4e4032
          have b4e4069 : ∀ X0 : G, y = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b4e4053 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e4053
            | exact resolve b4e4053 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4053
          have b4e4106 : ∀ X0 : G, y = (k (M.op y X0) X0) := by
            intro X0
            first
            | (have i₁ := b4e4069 X0
               have i₂ := b4e40 X0
               grind)
            | (have i₁ := b4e4069 y
               have i₂ := b4e40 y
               grind)
            | exact superpose b4e40 b4e4069
            | exact resolve b4e4069 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4069
          have b4e5884 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ y = (M.op y (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e396 (σ X0) (σ X0)
               have i₂ := b4e75 X1 X0
               grind)
            | exact superpose b4e75 b4e396
            | (have j1 := b4e75 X1 X0
               grind)
            | exact resolve b4e396 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e6358 : ∀ X0 : G, (τ y) = (k (τ (M.op y (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op y (σ X0)) X0
               have i₂ := b4e4106 (σ X0)
               grind)
            | exact superpose b4e4106 b4e30
            | exact resolve b4e30 b4e4106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e4106
          have b4e6370 : ∀ X0 : G, y = (k (τ (M.op y (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b4e6358 X0
               have i₂ := b4e264
               grind)
            | exact superpose b4e264 b4e6358
            | exact resolve b4e6358 b4e264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6358
          have b4e6407 : ∀ X0 : G, y ≠ (M.op y X0) ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e57 X0
               have i₂ := b4e40 X0
               grind)
            | (have i₁ := b4e57 y
               have i₂ := b4e40 y
               grind)
            | exact superpose b4e40 b4e57
            | (have j0 := b4e57 X0
               grind)
            | exact resolve b4e57 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e15521 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ y = (M.op (σ X0) y) ∨ y = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e263 X0
               have i₂ := b4e1099 (σ X0) y
               grind)
            | exact superpose b4e1099 b4e263
            | (have j1 := b4e1099 (σ X0) y
               grind)
            | exact resolve b4e263 b4e1099
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1099
          have b4e15589 : ∀ X0 : G, y = (M.op y (σ X0)) ∨ (σ (k y X0)) = (M.op y (σ X0)) ∨ y = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e15521 X0
               have i₂ := b4e40 (σ X0)
               grind)
            | exact superpose b4e40 b4e15521
            | (have j0 := b4e15521 X0
               grind)
            | exact resolve b4e15521 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e15521
          have b4e15590 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ y = (M.op y (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e15589 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15589
          have b4e20516 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ y = (M.op y X0) ∨ (τ X1) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e396 X0 X0
               have i₂ := b4e76 X1 X0
               grind)
            | exact superpose b4e76 b4e396
            | (have j1 := b4e76 X1 X0
               grind)
            | exact resolve b4e396 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e396
          have b4e156897 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op y X0)) ∨ y = (M.op y X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e20516 X0 y
               have i₂ := b4e264
               grind)
            | exact superpose b4e264 b4e20516
            | (have j0 := b4e20516 X0 x
               grind)
            | exact resolve b4e20516 b4e264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20516
          have b4e156928 : ∀ X0 : G, (k y (σ X0)) = (σ (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b4e156897 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156897
          have b4e156942 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e156928 X0
               have i₂ := b4e263 X0
               grind)
            | exact superpose b4e263 b4e156928
            | (have j0 := b4e156928 X0
               grind)
            | exact resolve b4e156928 b4e263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e263 b4e156928
          have b4e169386 : (σ (M.op y x)) ≠ (σ (k y x)) ∨ y = (M.op y (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e148
               have i₂ := b4e5884 x y
               grind)
            | exact superpose b4e5884 b4e148
            | (have j1 := b4e5884 x y
               grind)
            | exact resolve b4e148 b4e5884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148 b4e5884
          have b4e169468 : y = (M.op y (σ x)) ∨ (σ (M.op y x)) ≠ (σ (k y x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e169386
               have i₂ := b4e248
               grind)
            | exact superpose b4e248 b4e169386
            | exact resolve b4e169386 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169386
          have b4e169469 : (σ (M.op y x)) ≠ (σ (k y x)) ∨ y = (M.op y (σ x)) := by grind
          clear b4e169468
          have b4e191236 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ y = (M.op y (σ x)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e169469
               have i₂ := b4e156942 x
               grind)
            | exact superpose b4e156942 b4e169469
            | (have j1 := b4e156942 (σ x)
               grind)
            | (have r₁ := b4e169469
               have r₂ := b4e156942 x
               grind)
            | exact resolve b4e169469 b4e156942
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156942 b4e169469
          have b4e191242 : y = (M.op y (σ x)) ∨ y = (M.op y x) := by grind
          clear b4e191236
          have b4e191290 : y = (k (τ y) x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e6370 x
               have i₂ := b4e191242
               grind)
            | exact superpose b4e191242 b4e6370
            | exact resolve b4e6370 b4e191242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6370 b4e191242
          have b4e191454 : y = (k y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e191290
               have i₂ := b4e264
               grind)
            | exact superpose b4e264 b4e191290
            | exact resolve b4e191290 b4e264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264 b4e191290
          have b4e191477 : y = (k y x) := by
            first
            | (have j1 := b4e6407 x
               grind)
            | (have r₁ := b4e191454
               have r₂ := b4e6407 x
               grind)
            | exact resolve b4e191454 b4e6407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6407 b4e191454
          have b4e191588 : (σ y) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e15590 x
               have i₂ := b4e191477
               grind)
            | exact superpose b4e191477 b4e15590
            | (have j0 := b4e15590 x
               grind)
            | exact resolve b4e15590 b4e191477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15590
          have b4e191662 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e419 x y
               have i₂ := b4e191477
               grind)
            | exact superpose b4e191477 b4e419
            | (have j0 := b4e419 x y
               grind)
            | exact resolve b4e419 b4e191477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e419 b4e191477
          have b4e191708 : y = (M.op y x) := by grind
          clear b4e191662
          have b4e191768 : y = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e191588
               have i₂ := b4e248
               grind)
            | exact superpose b4e248 b4e191588
            | exact resolve b4e191588 b4e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191588
          have b4e191769 : y = (M.op y (σ x)) := by grind
          clear b4e191768
          have b4e191831 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e267
               have i₂ := b4e191708
               grind)
            | exact superpose b4e191708 b4e267
            | exact resolve b4e267 b4e191708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e267 b4e191708
          have b4e192026 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e191831
               have i₂ := b4e191769
               grind)
            | exact superpose b4e191769 b4e191831
            | exact resolve b4e191831 b4e191769
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191769 b4e191831
          have b4e192047 : False := by grind
          exact b4e192047
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e31 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 X3
               have i₂ := b5e13 X2 X0 X1
               grind)
            | (have i₁ := b5e13 (M.op X1 X2) X1 X2
               have i₂ := b5e13 (M.op X1 X1) X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
          have b5e42 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 y
               have i₂ := b5e36 X0
               grind)
            | (have i₁ := b5e13 X0 y X0
               have i₂ := b5e36 X0
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 X0 X1
               have i₂ := b5e31 X1 X0
               grind)
            | exact superpose b5e31 b5e42
            | exact resolve b5e42 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 (M.op X1 X2) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | (have i₁ := b5e16 X0 (M.op X1 X1)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 (M.op X1 X2) X0
               grind)
            | (have r₁ := b5e16 (M.op X0 (M.op X0 X0)) X0
               have r₂ := b5e13 X0 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 y) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e51 X0 X1 X2
               have i₂ := b5e46 X1 X0
               grind)
            | exact superpose b5e46 b5e51
            | (have j0 := b5e51 X0 X1 X2
               grind)
            | (have r₁ := b5e51 X1 X1 y
               have r₂ := b5e46 X1 X1
               grind)
            | exact resolve b5e51 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e51
          have b5e77 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e77 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e189 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 X2 y
               have i₂ := b5e36 X0
               grind)
            | (have i₁ := b5e34 y X1 X2 X0
               have i₂ := b5e36 X0
               grind)
            | exact superpose b5e36 b5e34
            | exact resolve b5e34 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e232 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e189 X0 X1 X2
               have i₂ := b5e31 X2 X0
               grind)
            | exact superpose b5e31 b5e189
            | exact resolve b5e189 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e189
          have b5e3821 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have j0 := b5e53 X0 X0 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e3822 : ∀ X0 : G, (M.op (M.op X0 y) y) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b5e3821 X0
               have i₂ := b5e232 X0 y (M.op X0 y)
               grind)
            | exact superpose b5e232 b5e3821
            | exact resolve b5e3821 b5e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3821
          have b5e3842 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b5e3822 X0
               have i₂ := b5e232 X0 y y
               grind)
            | exact superpose b5e232 b5e3822
            | exact resolve b5e3822 b5e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e232 b5e3822
          have b5e3857 : ∀ X0 : G, y = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b5e3842 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3842
            | exact resolve b5e3842 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3842
          have b5e3913 : ∀ X0 : G, (σ y) = (k (σ (M.op (τ X0) y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e26 X0 (M.op (τ X0) y)
               have i₂ := b5e3857 (τ X0)
               grind)
            | exact superpose b5e3857 b5e26
            | exact resolve b5e26 b5e3857
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e3857
          have b5e3915 : ∀ X0 : G, (σ y) = (k (σ (M.op y (τ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b5e3913 X0
               have i₂ := b5e36 (τ X0)
               grind)
            | exact superpose b5e36 b5e3913
            | exact resolve b5e3913 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e3913
          have b5e5325 : (σ y) = (M.op (σ (M.op y (τ (σ y)))) (σ y)) ∨ (σ (M.op y (τ (σ y)))) = (M.op (σ (M.op y (τ (σ y)))) (σ y)) := by
            first
            | (have i₁ := b5e78 (σ (M.op y (τ (σ y))))
               have i₂ := b5e3915 (σ y)
               grind)
            | exact superpose b5e3915 b5e78
            | (have j0 := b5e78 (σ (M.op y (τ (σ y))))
               grind)
            | exact resolve b5e78 b5e3915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78 b5e3915
          have b5e5331 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ (M.op y (τ (σ y)))) = (M.op (σ (M.op y (τ (σ y)))) (σ y)) := by
            first
            | (have i₁ := b5e5325
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e5325
            | exact resolve b5e5325 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5325
          have b5e5345 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y (τ (σ y)))) = (M.op (σ (M.op y (τ (σ y)))) (σ y)) := by
            first
            | (have i₁ := b5e5331
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5331
            | exact resolve b5e5331 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5331
          have b5e5350 : (σ (M.op y (τ (σ y)))) = (M.op (σ (M.op y (τ (σ y)))) (σ y)) := by
            first
            | (have r₁ := b5e5345
               have r₂ := b5e24
               grind)
            | exact resolve b5e5345 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5345
          have b5e5354 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b5e5350
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e5350
            | exact resolve b5e5350 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5350
          have b5e5356 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e5354
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5354
            | exact resolve b5e5354 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5354
          have b5e5358 : False := by grind
          exact b5e5358
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 X0 X3
             have i₂ := b6e12 X2 X0 X1
             grind)
          | (have i₁ := b6e12 (M.op X1 X2) X1 X2
             have i₂ := b6e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op (σ x) X0) := by
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
        have b6e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X0 X0) X2 X3
             have i₂ := b6e12 (M.op X2 X3) X0 X1
             grind)
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e24 X0 X1
             grind)
          | exact superpose b6e24 b6e13
          | exact resolve b6e13 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e38 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op X1 X2) X0
             have i₂ := b6e12 X0 X1 X2
             grind)
          | (have i₁ := b6e15 X0 (M.op X1 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X1 X2) X0
             grind)
          | (have r₁ := b6e15 (M.op X0 (M.op X0 X0)) X0
             have r₂ := b6e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e42 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e41
          | exact resolve b6e41 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e25 X1 X0
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ (k x y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (σ x) X1
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e12
          | exact resolve b6e12 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X1 X0
             have j1 := b6e17 X2 X0
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X1 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e65 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e95 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 (σ x) X0 X1 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e28
          | exact resolve b6e28 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e134 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b6e30 X0
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e30
          | exact resolve b6e30 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e140 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) = (M.op (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e30 (M.op X0 X1)
             have i₂ := b6e12 (M.op (σ x) (σ x)) X0 X1
             grind)
          | (have i₁ := b6e30 X0
             have i₂ := b6e12 X0 (σ x) x
             grind)
          | exact superpose b6e12 b6e30
          | exact resolve b6e30 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e146 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e28 X0 (M.op (σ x) (σ x)) X1 X2
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e28
          | exact resolve b6e28 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e148 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op (σ x) (σ x))
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e155 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e148 X0 X1
             have i₂ := b6e95 X0 X1
             grind)
          | exact superpose b6e95 b6e148
          | exact resolve b6e148 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e148
        have b6e157 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e146 X0 X1 X2
             have i₂ := b6e95 X0 X1
             grind)
          | exact superpose b6e95 b6e146
          | exact resolve b6e146 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95 b6e146
        have b6e161 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op X0 X0) (σ (k x y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e140 X0 X1
             have i₂ := b6e54 (M.op X0 X0) (σ x)
             grind)
          | exact superpose b6e54 b6e140
          | exact resolve b6e140 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e140
        have b6e167 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ x) (σ (k x y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e161 X0 X1
             have i₂ := b6e157 X0 (σ (k x y)) X0
             grind)
          | exact superpose b6e157 b6e161
          | exact resolve b6e161 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161
        have b6e169 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e167 X0 X1
             have i₂ := b6e134 (σ x)
             grind)
          | exact superpose b6e134 b6e167
          | exact resolve b6e167 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e167
        have b6e170 : ∀ X0 X1 : G, (σ (k x y)) = (M.op (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e169 X0 X1
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e169
          | exact resolve b6e169 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e169
        have b6e541 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X1 X2) (M.op X0 X3)) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e33 X1 X2 X0 X3
             have i₂ := b6e17 X4 X0
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 X4 X0
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e639 : ∀ X0 X1 X3 X4 : G, (M.op (σ x) (M.op X0 X3)) = (M.op (M.op X1 X1) X0) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
          intro X0 X1 X3 X4
          first
          | (have i₁ := b6e541 X0 X1 x X3 X4
             have i₂ := b6e157 X1 (M.op X0 X3) x
             grind)
          | exact superpose b6e157 b6e541
          | (have j0 := b6e541 X0 X1 x X3 X4
             grind)
          | exact resolve b6e541 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541
        have b6e724 : ∀ X0 X3 X4 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 X3)) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
          intro X0 X3 X4
          first
          | (have i₁ := b6e639 X0 x X3 X4
             have i₂ := b6e157 x X0 x
             grind)
          | exact superpose b6e157 b6e639
          | (have j0 := b6e639 X0 x X3 X4
             grind)
          | exact resolve b6e639 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e639
        have b6e793 : ∀ X0 X4 : G, (M.op (σ x) X0) = (σ (k x y)) ∨ (M.op X4 X0) = (k X4 X0) ∨ (M.op X4 X0) = X4 := by
          intro X0 X4
          first
          | (have i₁ := b6e724 X0 x X4
             have i₂ := b6e170 X0 x
             grind)
          | exact superpose b6e170 b6e724
          | (have j0 := b6e724 X0 x X4
             grind)
          | exact resolve b6e724 b6e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e724
        have b6e1459 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b6e134 X0
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e134
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e134 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e1528 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have j0 := b6e1459 X0
             grind)
          | (have r₁ := b6e1459 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e1459 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1459
        have b6e1552 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (M.op x y))) := by
          intro X0
          first
          | (have j0 := b6e1528 X0
             grind)
          | (have r₁ := b6e1528 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e1528 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1528
        have b6e4240 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b6e40 X0 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e4241 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e4240 X0
             have i₂ := b6e12 (M.op X0 (M.op X0 X0)) X0 (M.op X0 X0)
             grind)
          | exact superpose b6e12 b6e4240
          | exact resolve b6e4240 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4240
        have b6e4319 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b6e4241 X0
             have i₂ := b6e12 (M.op X0 X0) X0 (M.op X0 X0)
             grind)
          | exact superpose b6e12 b6e4241
          | exact resolve b6e4241 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4241
        have b6e4397 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e4319 X0
             have i₂ := b6e155 X0 X0
             grind)
          | exact superpose b6e155 b6e4319
          | exact resolve b6e4319 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4319
        have b6e4471 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (k (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e4397 X0
             have i₂ := b6e157 X0 (M.op X0 X0) X0
             grind)
          | exact superpose b6e157 b6e4397
          | exact resolve b6e4397 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4397
        have b6e4527 : ∀ X0 : G, (σ (k x y)) = (k (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e4471 X0
             have i₂ := b6e170 X0 X0
             grind)
          | exact superpose b6e170 b6e4471
          | exact resolve b6e4471 b6e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4471
        have b6e4650 : ∀ X0 : G, (k (τ (M.op (σ x) (σ X0))) X0) = (τ (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b6e37 (M.op (σ x) (σ X0)) X0
             have i₂ := b6e4527 (σ X0)
             grind)
          | exact superpose b6e4527 b6e37
          | exact resolve b6e37 b6e4527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4651 : ∀ X0 : G, (k (σ (M.op (σ x) (τ X0))) X0) = (σ (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b6e25 X0 (M.op (σ x) (τ X0))
             have i₂ := b6e4527 (τ X0)
             grind)
          | exact superpose b6e4527 b6e25
          | exact resolve b6e25 b6e4527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4527
        have b6e4652 : ∀ X0 : G, (k x y) = (k (τ (M.op (σ x) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b6e4650 X0
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e4650
          | exact resolve b6e4650 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4650
        have b6e7014 : (k x y) = (k (τ (M.op (σ x) (σ x))) (M.op x y)) := by
          first
          | (have i₁ := b6e4652 (M.op x y)
             have i₂ := b6e1552 (σ x)
             grind)
          | exact superpose b6e1552 b6e4652
          | exact resolve b6e4652 b6e1552
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1552 b6e4652
        have b6e7049 : (k x y) = (k (τ (σ (k x y))) (M.op x y)) := by
          first
          | (have i₁ := b6e7014
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e7014
          | exact resolve b6e7014 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e7014
        have b6e7065 : (k x y) = (k (k x y) (M.op x y)) := by
          first
          | (have i₁ := b6e7049
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e7049
          | exact resolve b6e7049 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7049
        have b6e7633 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e7065
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e7065
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e7065 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7065
        have b6e7666 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e7633
             have r₂ := b6e21
             grind)
          | exact resolve b6e7633 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7633
        have b6e7675 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
          first
          | (have r₁ := b6e7666
             have r₂ := b6e20
             grind)
          | exact resolve b6e7666 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7666
        have b6e8868 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b6e17 (M.op x y) (M.op x y)
             have i₂ := b6e7675
             grind)
          | exact superpose b6e7675 b6e17
          | (have j0 := b6e17 (M.op x y) (M.op x y)
             grind)
          | exact resolve b6e17 b6e7675
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7675
        have b6e8869 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
        clear b6e8868
        have b6e8880 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
          first
          | (have i₁ := b6e8869
             have i₂ := b6e157 x (M.op x y) y
             grind)
          | exact superpose b6e157 b6e8869
          | exact resolve b6e8869 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8869
        have b6e8890 : (M.op x y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e8880
             have i₂ := b6e170 x y
             grind)
          | exact superpose b6e170 b6e8880
          | exact resolve b6e8880 b6e170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e170 b6e8880
        have b6e8997 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e8890
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e8890
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e8890 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e9004 : (k x y) = (τ (M.op x y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e8890
             grind)
          | exact superpose b6e8890 b6e13
          | exact resolve b6e13 b6e8890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e9020 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e8997
             have r₂ := b6e21
             grind)
          | exact resolve b6e8997 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8997
        have b6e9029 : (M.op x y) = (σ (M.op x y)) := by
          first
          | (have r₁ := b6e9020
             have r₂ := b6e20
             grind)
          | exact resolve b6e9020 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9020
        have b6e9183 : (M.op x y) ≠ (σ x) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e9029
             grind)
          | exact superpose b6e9029 b6e23
          | exact resolve b6e23 b6e9029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e9184 : (M.op x y) = (τ (M.op x y)) := by
          first
          | (have i₁ := b6e13 (M.op x y)
             have i₂ := b6e9029
             grind)
          | exact superpose b6e9029 b6e13
          | exact resolve b6e13 b6e9029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e9190 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (M.op x y) X0)) := by
          intro X0
          first
          | (have i₁ := b6e48 (M.op x y) X0
             have i₂ := b6e9029
             grind)
          | exact superpose b6e9029 b6e48
          | exact resolve b6e48 b6e9029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e9363 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e9004
             have i₂ := b6e9184
             grind)
          | exact superpose b6e9184 b6e9004
          | exact resolve b6e9004 b6e9184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9184
        have b6e9483 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = (k X0 y) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e73 y x X0
             have i₂ := b6e9363
             grind)
          | exact superpose b6e9363 b6e73
          | (have j0 := b6e73 y x X0
             grind)
          | exact resolve b6e73 b6e9363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e9484 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e9483 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9483
        have b6e9486 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e9484 X0
             grind)
          | (have r₁ := b6e9484 X0
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e9484 x
             have r₂ := b6e20
             grind)
          | exact resolve b6e9484 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9484
        have b6e19974 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e793 (σ y) X0
             grind)
          | exact superpose b6e793 b6e22
          | (have j1 := b6e793 (σ y) X0
             grind)
          | exact resolve b6e22 b6e793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e793
        have b6e20129 : ∀ X0 : G, (M.op x y) = (σ x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e19974 X0
             have i₂ := b6e8890
             grind)
          | exact superpose b6e8890 b6e19974
          | (have j0 := b6e19974 X0
             grind)
          | exact resolve b6e19974 b6e8890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e19974
        have b6e20225 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e20129 X0
             grind)
          | (have r₁ := b6e20129 X0
             have r₂ := b6e9183
             grind)
          | exact resolve b6e20129 b6e9183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e20129
        have b6e38188 : ∀ X0 : G, (σ (σ (σ (k x y)))) = (k (σ (σ (M.op (σ x) (τ (τ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e25 X0 (σ (M.op (σ x) (τ (τ X0))))
             have i₂ := b6e4651 (τ X0)
             grind)
          | exact superpose b6e4651 b6e25
          | exact resolve b6e25 b6e4651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e4651
        have b6e38193 : ∀ X0 : G, (σ (σ (M.op x y))) = (k (σ (σ (M.op (σ x) (τ (τ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e38188 X0
             have i₂ := b6e8890
             grind)
          | exact superpose b6e8890 b6e38188
          | exact resolve b6e38188 b6e8890
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8890 b6e38188
        have b6e38287 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (σ (M.op (σ x) (τ (τ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e38193 X0
             have i₂ := b6e9029
             grind)
          | exact superpose b6e9029 b6e38193
          | exact resolve b6e38193 b6e9029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38193
        have b6e38364 : ∀ X0 : G, (M.op x y) = (k (σ (σ (M.op (σ x) (τ (τ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e38287 X0
             have i₂ := b6e9029
             grind)
          | exact superpose b6e9029 b6e38287
          | exact resolve b6e38287 b6e9029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9029 b6e38287
        have b6e41875 : ∀ X0 : G, (τ (M.op x y)) = (k (τ (σ (σ (M.op (σ x) (τ (τ (σ X0))))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e37 (σ (σ (M.op (σ x) (τ (τ (σ X0)))))) X0
             have i₂ := b6e38364 (σ X0)
             grind)
          | exact superpose b6e38364 b6e37
          | exact resolve b6e37 b6e38364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38364
        have b6e41896 : ∀ X0 : G, (τ (M.op x y)) = (k (σ (M.op (σ x) (τ (τ (σ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e41875 X0
             have i₂ := b6e13 (σ (M.op (σ x) (τ (τ (σ X0)))))
             grind)
          | exact superpose b6e13 b6e41875
          | exact resolve b6e41875 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41875
        have b6e41967 : ∀ X0 : G, (k (σ (M.op (σ x) (τ X0))) X0) = (τ (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b6e41896 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e41896
          | exact resolve b6e41896 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41896
        have b6e42026 : ∀ X0 : G, (k x y) = (k (σ (M.op (σ x) (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b6e41967 X0
             have i₂ := b6e9004
             grind)
          | exact superpose b6e9004 b6e41967
          | exact resolve b6e41967 b6e9004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41967
        have b6e42069 : ∀ X0 : G, (M.op x y) = (k (σ (M.op (σ x) (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b6e42026 X0
             have i₂ := b6e9363
             grind)
          | exact superpose b6e9363 b6e42026
          | exact resolve b6e42026 b6e9363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42026
        have b6e43412 : ∀ X0 : G, (τ (M.op x y)) = (k (τ (σ (M.op (σ x) (τ (σ X0))))) X0) := by
          intro X0
          first
          | (have i₁ := b6e37 (σ (M.op (σ x) (τ (σ X0)))) X0
             have i₂ := b6e42069 (σ X0)
             grind)
          | exact superpose b6e42069 b6e37
          | exact resolve b6e37 b6e42069
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37 b6e42069
        have b6e43433 : ∀ X0 : G, (τ (M.op x y)) = (k (M.op (σ x) (τ (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b6e43412 X0
             have i₂ := b6e13 (M.op (σ x) (τ (σ X0)))
             grind)
          | exact superpose b6e13 b6e43412
          | exact resolve b6e43412 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43412
        have b6e43503 : ∀ X0 : G, (k (M.op (σ x) X0) X0) = (τ (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b6e43433 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e43433
          | exact resolve b6e43433 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43433
        have b6e43549 : ∀ X0 : G, (k x y) = (k (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e43503 X0
             have i₂ := b6e9004
             grind)
          | exact superpose b6e9004 b6e43503
          | exact resolve b6e43503 b6e9004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9004 b6e43503
        have b6e43577 : ∀ X0 : G, (M.op x y) = (k (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e43549 X0
             have i₂ := b6e9363
             grind)
          | exact superpose b6e9363 b6e43549
          | exact resolve b6e43549 b6e9363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9363 b6e43549
        have b6e64041 : (τ (M.op (M.op x y) (σ y))) = (k (M.op x y) (τ (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
          first
          | (have i₁ := b6e9190 (σ y)
             have i₂ := b6e20225 (M.op x y)
             grind)
          | exact superpose b6e20225 b6e9190
          | (have j1 := b6e20225 (M.op x y)
             grind)
          | exact resolve b6e9190 b6e20225
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9190 b6e20225
        have b6e64093 : (k (M.op x y) y) = (τ (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
          first
          | (have i₁ := b6e64041
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e64041
          | exact resolve b6e64041 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64041
        have b6e64112 : (k (M.op x y) y) = (τ (M.op (σ y) (M.op x x))) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
          first
          | (have i₁ := b6e64093
             have i₂ := b6e12 (σ y) x y
             grind)
          | exact superpose b6e12 b6e64093
          | exact resolve b6e64093 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64093
        have b6e64125 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
          first
          | (have i₁ := b6e64112
             have i₂ := b6e155 x (σ y)
             grind)
          | exact superpose b6e155 b6e64112
          | exact resolve b6e64112 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64112
        have b6e64135 : (τ (σ x)) = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
          first
          | (have i₁ := b6e64125
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64125
          | exact resolve b6e64125 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64125
        have b6e64143 : x = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
          first
          | (have i₁ := b6e64135
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e64135
          | exact resolve b6e64135 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64135
        have b6e64150 : (M.op x y) = (M.op (σ y) (M.op x x)) ∨ x = (k (M.op x y) y) := by
          first
          | (have i₁ := b6e64143
             have i₂ := b6e12 (σ y) x y
             grind)
          | exact superpose b6e12 b6e64143
          | exact resolve b6e64143 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64143
        have b6e64157 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) y) := by
          first
          | (have i₁ := b6e64150
             have i₂ := b6e155 x (σ y)
             grind)
          | exact superpose b6e155 b6e64150
          | exact resolve b6e64150 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64150
        have b6e64164 : (M.op x y) = (σ x) ∨ x = (k (M.op x y) y) := by
          first
          | (have i₁ := b6e64157
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64157
          | exact resolve b6e64157 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64157
        have b6e64168 : x = (k (M.op x y) y) := by
          first
          | (have r₁ := b6e64164
             have r₂ := b6e9183
             grind)
          | exact resolve b6e64164 b6e9183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9183 b6e64164
        have b6e64399 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
          first
          | (have i₁ := b6e9486 (M.op x y)
             have i₂ := b6e64168
             grind)
          | exact superpose b6e64168 b6e9486
          | (have j0 := b6e9486 (M.op x y)
             grind)
          | exact resolve b6e9486 b6e64168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9486
        have b6e64433 : x = (M.op y (M.op x x)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
          first
          | (have i₁ := b6e64399
             have i₂ := b6e12 y x y
             grind)
          | exact superpose b6e12 b6e64399
          | exact resolve b6e64399 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64399
        have b6e64460 : x = (M.op (σ x) y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
          first
          | (have i₁ := b6e64433
             have i₂ := b6e155 x y
             grind)
          | exact superpose b6e155 b6e64433
          | exact resolve b6e64433 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64433
        have b6e64486 : (M.op x y) = (M.op y (M.op x x)) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e64460
             have i₂ := b6e12 y x y
             grind)
          | exact superpose b6e12 b6e64460
          | exact resolve b6e64460 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64460
        have b6e64512 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e64486
             have i₂ := b6e155 x y
             grind)
          | exact superpose b6e155 b6e64486
          | exact resolve b6e64486 b6e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e155 b6e64486
        have b6e68442 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e43577 y
             have i₂ := b6e64512
             grind)
          | exact superpose b6e64512 b6e43577
          | exact resolve b6e43577 b6e64512
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43577 b6e64512
        have b6e68545 : x = (M.op x y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e68442
             have i₂ := b6e64168
             grind)
          | exact superpose b6e64168 b6e68442
          | exact resolve b6e68442 b6e64168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64168 b6e68442
        have b6e68565 : x = (M.op (σ x) y) := by
          first
          | (have r₁ := b6e68545
             have r₂ := b6e20
             grind)
          | exact resolve b6e68545 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68545
        have b6e69231 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e157 (σ x) X0 y
             have i₂ := b6e68565
             grind)
          | exact superpose b6e68565 b6e157
          | exact resolve b6e157 b6e68565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157
        have b6e71002 : x = (M.op x y) := by
          first
          | (have i₁ := b6e68565
             have i₂ := b6e69231 y
             grind)
          | exact superpose b6e69231 b6e68565
          | exact resolve b6e68565 b6e69231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68565 b6e69231
        have b6e71003 : False := by grind
        exact b6e71003
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e48 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
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
          have b7e53 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b7e48
          have b7e56 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e53
            | exact resolve b7e53 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e59 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e14
            | exact resolve b7e14 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : y = (k y y) := by
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
          have b7e78 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e60
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e60 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e89 : y = (M.op y y) := by grind
          clear b7e78
          have b7e94 : False := by grind
          exact b7e94
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e3944 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e73 x y
               grind)
            | exact superpose b8e73 b8e20
            | (have j1 := b8e73 y y
               grind)
            | exact resolve b8e20 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e4072 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e3944
               have r₂ := b8e24
               grind)
            | exact resolve b8e3944 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3944
          have b8e4077 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e4072
               have r₂ := b8e23
               grind)
            | exact resolve b8e4072 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4072
          have b8e4082 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e4077
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e4077
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e4077 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4077
          have b8e4083 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e4082
          have b8e4087 : x = (M.op x y) := by
            first
            | (have r₁ := b8e4083
               have r₂ := b8e22
               grind)
            | exact resolve b8e4083 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4083
          have b8e4092 : False := by grind
          exact b8e4092

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y x) := by grind
        have b0e21 : (σ x) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : y = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b0e12 X0 X2 X3
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e34 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 := by
          intro X0
          first
          | (have i₁ := b0e12 X0 (σ y) (σ x)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e12
          | exact resolve b0e12 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
          intro X0
          first
          | (have i₁ := b0e12 X0 y x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e65 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b0e36 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e36
          | exact resolve b0e36 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e162 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b0e33 X0 X0 x x
             have i₂ := b0e12 X0 x x
             grind)
          | exact superpose b0e12 b0e33
          | exact resolve b0e33 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33
        have b0e176 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e34 (σ x)
             have i₂ := b0e162 (σ x)
             grind)
          | exact superpose b0e162 b0e34
          | exact resolve b0e34 b0e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e34
        have b0e177 : x = (M.op x x) := by
          first
          | (have i₁ := b0e36 x
             have i₂ := b0e162 x
             grind)
          | exact superpose b0e162 b0e36
          | exact resolve b0e36 b0e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36 b0e162
        have b0e226 : y = (M.op y x) := by
          first
          | (have i₁ := b0e65
             have i₂ := b0e177
             grind)
          | exact superpose b0e177 b0e65
          | exact resolve b0e65 b0e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e65 b0e177
        have b0e238 : x = y := by
          first
          | (have i₁ := b0e226
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e226
          | exact resolve b0e226 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e226
        have b0e306 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e23
             have i₂ := b0e238
             grind)
          | exact superpose b0e238 b0e23
          | exact resolve b0e23 b0e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23 b0e238
        have b0e315 : False := by grind
        exact b0e315
      · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b1e21 : x = (M.op y x) := by grind
          have b1e23 : y ≠ (M.op x y) := by grind
          have b1e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : x ≠ y := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e23
            | exact resolve b1e23 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e41 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 := by
            intro X0
            first
            | (have i₁ := b1e13 X0 x y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
            intro X0
            first
            | (have i₁ := b1e13 X0 y x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e48 : x = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b1e41 x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e41
            | exact resolve b1e41 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41
          have b1e75 : y = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b1e42 y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e42
            | exact resolve b1e42 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e76 : x = (M.op x x) := by
            first
            | (have i₁ := b1e42 x
               have i₂ := b1e48
               grind)
            | exact superpose b1e48 b1e42
            | exact resolve b1e42 b1e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42 b1e48
          have b1e82 : y = (M.op y x) := by
            first
            | (have i₁ := b1e75
               have i₂ := b1e76
               grind)
            | exact superpose b1e76 b1e75
            | exact resolve b1e75 b1e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e75 b1e76
          have b1e83 : x = y := by
            first
            | (have i₁ := b1e82
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e82
            | exact resolve b1e82 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e82
          have b1e84 : False := by grind
          exact b1e84
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e21 : x = (M.op y x) := by grind
          have b2e24 : x ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e36 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 y x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e38 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b2e13 X0 X2 X3
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e43 : y = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b2e36 y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e36
            | exact resolve b2e36 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e142 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b2e38 X0 X0 x x
               have i₂ := b2e13 X0 x x
               grind)
            | exact superpose b2e13 b2e38
            | exact resolve b2e38 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e38
          have b2e157 : x = (M.op x x) := by
            first
            | (have i₁ := b2e36 x
               have i₂ := b2e142 x
               grind)
            | exact superpose b2e142 b2e36
            | exact resolve b2e36 b2e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e142
          have b2e194 : y = (M.op y x) := by
            first
            | (have i₁ := b2e43
               have i₂ := b2e157
               grind)
            | exact superpose b2e157 b2e43
            | exact resolve b2e43 b2e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43
          have b2e206 : x = y := by
            first
            | (have i₁ := b2e194
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e194
            | exact resolve b2e194 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e194
          have b2e251 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e206
               grind)
            | exact superpose b2e206 b2e24
            | exact resolve b2e24 b2e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e206
          have b2e256 : False := by grind
          exact b2e256
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : x = (M.op y x) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b3e49 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e50 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b3e49
          have b3e53 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e50
               have r₂ := b3e25
               grind)
            | exact resolve b3e50 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e50
          have b3e54 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e53
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e53
            | exact resolve b3e53 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e53
          have b3e55 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e54
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e54
            | exact resolve b3e54 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e54
          have b3e56 : False := by grind
          exact b3e56
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e23
              | exact resolve b4e23 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : x ≠ x ∨ y = (k x y) := by
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
            have b4e33 : y = (k x y) := by grind
            clear b4e30
            have b4e51 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e18 (σ x) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e54 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b4e51
            have b4e58 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e54
                 have r₂ := b4e28
                 grind)
              | exact resolve b4e54 b4e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e54
            have b4e59 : (σ x) = (σ (k x y)) := by
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
            have b4e60 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e59
                 have i₂ := b4e33
                 grind)
              | exact superpose b4e33 b4e59
              | exact resolve b4e59 b4e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33 b4e59
            have b4e61 : False := by grind
            exact b4e61
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : x = (M.op y x) := by grind
            have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e23
              | exact resolve b5e23 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
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
            have b5e44 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b5e18 (σ x) (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e18
              | (have j0 := b5e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b5e18 (σ x) (σ y)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e18 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e49 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b5e44
            have b5e50 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e49
                 have r₂ := b5e27
                 grind)
              | exact resolve b5e49 b5e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e49
            have b5e51 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b5e50
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e50
              | exact resolve b5e50 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e50
            have b5e52 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e51
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e51
              | exact resolve b5e51 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e51
            have b5e53 : False := by grind
            exact b5e53
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
          have b6e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e20
            | exact resolve b6e20 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e32 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
            intro X0
            first
            | (have i₁ := b6e13 X0 y x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e34 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b6e13 X0 X2 X3
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : y = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b6e32 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e32
            | exact resolve b6e32 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e18 (σ X1) (σ X0)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X1) (σ X0)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e128 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e34 X0 X0 x x
               have i₂ := b6e13 X0 x x
               grind)
            | exact superpose b6e13 b6e34
            | exact resolve b6e34 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
          have b6e142 : x = (M.op x x) := by
            first
            | (have i₁ := b6e32 x
               have i₂ := b6e128 x
               grind)
            | exact superpose b6e128 b6e32
            | exact resolve b6e32 b6e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32 b6e128
          have b6e184 : y = (M.op y x) := by
            first
            | (have i₁ := b6e39
               have i₂ := b6e142
               grind)
            | exact superpose b6e142 b6e39
            | exact resolve b6e39 b6e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39
          have b6e190 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b6e16 x x
               have i₂ := b6e142
               grind)
            | exact superpose b6e142 b6e16
            | (have j0 := b6e16 x x
               grind)
            | (have r₁ := b6e16 x x
               have r₂ := b6e142
               grind)
            | exact resolve b6e16 b6e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e142
          have b6e195 : x = (k x x) := by grind
          clear b6e190
          have b6e196 : x = y := by
            first
            | (have i₁ := b6e184
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e184
            | exact resolve b6e184 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e184
          have b6e255 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e25
               have i₂ := b6e196
               grind)
            | exact superpose b6e196 b6e25
            | exact resolve b6e25 b6e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e25 b6e196
          have b6e393 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e255
               have i₂ := b6e55 x x
               grind)
            | exact superpose b6e55 b6e255
            | (have j1 := b6e55 x x
               grind)
            | (have r₁ := b6e255
               have r₂ := b6e55 x x
               grind)
            | exact resolve b6e255 b6e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e55
          have b6e394 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e393
          have b6e395 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b6e394
               have r₂ := b6e255
               grind)
            | exact resolve b6e394 b6e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e255 b6e394
          have b6e396 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e395
               have i₂ := b6e195
               grind)
            | exact superpose b6e195 b6e395
            | exact resolve b6e395 b6e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e195 b6e395
          have b6e397 : False := by grind
          exact b6e397
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e22 : x = (M.op y x) := by grind
            have b7e25 : y ≠ (M.op x y) := by grind
            have b7e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : x ≠ y := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e25
              | exact resolve b7e25 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e34 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e35 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e41 : y = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b7e34 y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e34
              | exact resolve b7e34 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e67 : x = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b7e35 x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e35
              | exact resolve b7e35 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e35
            have b7e73 : x = (M.op x x) := by
              first
              | (have i₁ := b7e34 x
                 have i₂ := b7e67
                 grind)
              | exact superpose b7e67 b7e34
              | exact resolve b7e34 b7e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e34 b7e67
            have b7e86 : y = (M.op y x) := by
              first
              | (have i₁ := b7e41
                 have i₂ := b7e73
                 grind)
              | exact superpose b7e73 b7e41
              | exact resolve b7e41 b7e73
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e41 b7e73
            have b7e93 : x = y := by
              first
              | (have i₁ := b7e86
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e86
              | exact resolve b7e86 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e86
            have b7e94 : False := by grind
            exact b7e94
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e22 : x = (M.op y x) := by grind
            have b8e26 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
              intro X0
              first
              | (have i₁ := b8e14 X0 y x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
                 have i₂ := b8e14 X0 X2 X3
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e36 : y = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b8e31 y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e31
              | exact resolve b8e31 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e32 X0 X0 x x
                 have i₂ := b8e14 X0 x x
                 grind)
              | exact superpose b8e14 b8e32
              | exact resolve b8e32 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32
            have b8e101 : x = (M.op x x) := by
              first
              | (have i₁ := b8e31 x
                 have i₂ := b8e87 x
                 grind)
              | exact superpose b8e87 b8e31
              | exact resolve b8e31 b8e87
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31 b8e87
            have b8e131 : y = (M.op y x) := by
              first
              | (have i₁ := b8e36
                 have i₂ := b8e101
                 grind)
              | exact superpose b8e101 b8e36
              | exact resolve b8e36 b8e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36
            have b8e143 : x = y := by
              first
              | (have i₁ := b8e131
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e131
              | exact resolve b8e131 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e131
            have b8e179 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e143
                 grind)
              | exact superpose b8e143 b8e26
              | exact resolve b8e26 b8e143
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e143
            have b8e183 : False := by grind
            exact b8e183
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : x ≠ (M.op y x) := by grind
          have b9e22 : y = (M.op y x) := by grind
          have b9e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : x ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
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
          have b9e51 : y ≠ y ∨ x = y ∨ x = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e52 : x = y ∨ x = (k x y) := by grind
          clear b9e51
          have b9e54 : x = (k x y) := by
            first
            | (have r₁ := b9e52
               have r₂ := b9e25
               grind)
            | exact resolve b9e52 b9e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52
          have b9e56 : x = y := by
            first
            | (have i₁ := b9e38
               have i₂ := b9e54
               grind)
            | exact superpose b9e54 b9e38
            | exact resolve b9e38 b9e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e38 b9e54
          have b9e58 : False := by grind
          exact b9e58
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e23 : y = (M.op y x) := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : y ≠ (M.op x y) := by grind
            have b10e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : x ≠ y := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e25
              | exact resolve b10e25 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e32 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b10e33 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b10e32
            have b10e34 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b10e33
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e33
              | exact resolve b10e33 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e35 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e34
                 grind)
              | exact superpose b10e34 b10e15
              | exact resolve b10e15 b10e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34
            have b10e36 : y = (k x y) := by
              first
              | (have i₁ := b10e35
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e35
              | exact resolve b10e35 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e59 : y ≠ y ∨ x = y ∨ x = (k x y) := by
              first
              | (have i₁ := b10e18 x y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e18
              | (have j0 := b10e18 x y
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e23
                 grind)
              | exact resolve b10e18 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e60 : x = y ∨ x = (k x y) := by grind
            clear b10e59
            have b10e64 : x = (k x y) := by
              first
              | (have r₁ := b10e60
                 have r₂ := b10e27
                 grind)
              | exact resolve b10e60 b10e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e60
            have b10e67 : x = y := by
              first
              | (have i₁ := b10e36
                 have i₂ := b10e64
                 grind)
              | exact superpose b10e64 b10e36
              | exact resolve b10e36 b10e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36 b10e64
            have b10e69 : False := by grind
            exact b10e69
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : x ≠ (M.op y x) := by grind
            have b11e23 : y = (M.op y x) := by grind
            have b11e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : x ≠ y := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e22
              | exact resolve b11e22 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
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
            have b11e55 : y ≠ y ∨ x = y ∨ x = (k x y) := by
              first
              | (have i₁ := b11e18 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x y
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e60 : x = y ∨ x = (k x y) := by grind
            clear b11e55
            have b11e61 : x = (k x y) := by
              first
              | (have r₁ := b11e60
                 have r₂ := b11e27
                 grind)
              | exact resolve b11e60 b11e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e63 : x = y := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e61
                 grind)
              | exact superpose b11e61 b11e33
              | exact resolve b11e33 b11e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33 b11e61
            have b11e65 : False := by grind
            exact b11e65
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b12e22 : x ≠ (M.op y x) := by grind
            have b12e23 : y = (M.op y x) := by grind
            have b12e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : x ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e22
              | exact resolve b12e22 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e38 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e14 X0 x y
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e39 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e14 X0 y x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e45 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b12e38 x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e38
              | exact resolve b12e38 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e75 : y = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b12e39 y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e39
              | exact resolve b12e39 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e39
            have b12e81 : y = (M.op y y) := by
              first
              | (have i₁ := b12e38 y
                 have i₂ := b12e75
                 grind)
              | exact superpose b12e75 b12e38
              | exact resolve b12e38 b12e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e38 b12e75
            have b12e94 : x = (M.op x y) := by
              first
              | (have i₁ := b12e45
                 have i₂ := b12e81
                 grind)
              | exact superpose b12e81 b12e45
              | exact resolve b12e45 b12e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e45 b12e81
            have b12e101 : x = y := by
              first
              | (have i₁ := b12e94
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e94
              | exact resolve b12e94 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e94
            have b12e102 : False := by grind
            exact b12e102
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b13e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b13e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b13e27 : y ≠ (M.op x y) := by grind
              have b13e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : x ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e27
                | exact resolve b13e27 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e30 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b13e25
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e25
                | exact resolve b13e25 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e32 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e22
                | exact resolve b13e22 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e58 : x ≠ x ∨ x = y ∨ y = (k y x) := by
                first
                | (have i₁ := b13e19 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 y x
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e61 : x = y ∨ y = (k y x) := by grind
              clear b13e58
              have b13e66 : y = (k y x) := by
                first
                | (have r₁ := b13e61
                   have r₂ := b13e29
                   grind)
                | exact resolve b13e61 b13e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e29 b13e61
              have b13e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b13e368 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e18 (σ X0) (σ X1)
                   have i₂ := b13e71 X1 X0
                   grind)
                | exact superpose b13e71 b13e18
                | (have j0 := b13e18 (σ X0) (σ X1)
                   have j1 := b13e71 X1 X0
                   grind)
                | (have r₁ := b13e18 (σ X0) (σ X0)
                   have r₂ := b13e71 X0 X0
                   grind)
                | (have r₁ := b13e18 (σ X1) (σ X0)
                   have r₂ := b13e71 X0 X1
                   grind)
                | exact resolve b13e18 b13e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e71
              have b13e383 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b13e368 X0 X1
                   have j1 := b13e18 (σ X0) (σ X1)
                   grind)
                | (have r₁ := b13e368 X1 X1
                   have r₂ := b13e18 (σ X1) (σ X1)
                   grind)
                | (have r₁ := b13e368 X0 X1
                   have r₂ := b13e18 (σ X0) (σ X1)
                   grind)
                | exact resolve b13e368 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e368
              have b13e386 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e383 X0 X1
                   have i₂ := b13e21 X0 X1
                   grind)
                | exact superpose b13e21 b13e383
                | (have j0 := b13e383 X0 X1
                   grind)
                | exact resolve b13e383 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e383
              have b13e5279 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e386 y x
                   have i₂ := b13e66
                   grind)
                | exact superpose b13e66 b13e386
                | (have j0 := b13e386 y x
                   grind)
                | exact resolve b13e386 b13e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e66 b13e386
              have b13e5288 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
              clear b13e5279
              have b13e5304 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b13e5288
                   have r₂ := b13e30
                   grind)
                | exact resolve b13e5288 b13e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e5288
              have b13e5310 : False := by grind
              exact b13e5310
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b14e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b14e27 : y ≠ (M.op x y) := by grind
              have b14e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e25
                | exact resolve b14e25 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b14e37 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
                   have i₂ := b14e15 X0 X2 X3
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
                   have i₂ := b14e15 X0 X2 X3
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b14e85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k X0 (τ X1))
                   have i₂ := b14e34 X1 X0
                   grind)
                | exact superpose b14e34 b14e16
                | exact resolve b14e16 b14e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e34
              have b14e152 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have i₁ := b14e37 X0 X0 x x
                   have i₂ := b14e15 X0 x x
                   grind)
                | exact superpose b14e15 b14e37
                | exact resolve b14e37 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37
              have b14e164 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X1 X0 (M.op X0 X0)
                   have i₂ := b14e152 X0
                   grind)
                | exact superpose b14e152 b14e15
                | exact resolve b14e15 b14e152
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e190 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e40 X0 (M.op X0 X1) X0 X1
                   have i₂ := b14e152 (M.op X0 X1)
                   grind)
                | exact superpose b14e152 b14e40
                | exact resolve b14e40 b14e152
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40 b14e152
              have b14e313 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e59 x y
                   grind)
                | exact superpose b14e59 b14e22
                | (have j1 := b14e59 x y
                   grind)
                | exact resolve b14e22 b14e59
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59
              have b14e448 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e164 X0 (M.op X1 X0)
                   have i₂ := b14e15 X0 X1 X0
                   grind)
                | exact superpose b14e15 b14e164
                | exact resolve b14e164 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e164
              have b14e513 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e19 X0 (M.op X1 X0)
                   have i₂ := b14e448 X0 X1
                   grind)
                | exact superpose b14e448 b14e19
                | (have j0 := b14e19 X1 X0
                   grind)
                | (have r₁ := b14e19 X0 (M.op X1 X0)
                   have r₂ := b14e448 X0 X1
                   grind)
                | exact resolve b14e19 b14e448
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e448
              have b14e542 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e513 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e513
              have b14e666 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e85 X0 (M.op X1 (σ X0))
                   have i₂ := b14e542 X1 (σ X0)
                   grind)
                | exact superpose b14e542 b14e85
                | (have j1 := b14e542 X1 (σ X0)
                   grind)
                | exact resolve b14e85 b14e542
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e85 b14e542
              have b14e671 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e666 X0 X1
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e666
                | (have j0 := b14e666 X0 X1
                   grind)
                | exact resolve b14e666 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e666
              have b14e7548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b14e313
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e313
                | (have j1 := b14e20 (σ y) (σ x)
                   grind)
                | exact resolve b14e313 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e313
              have b14e7549 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
              clear b14e7548
              have b14e7550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b14e7549
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e7549 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7549
              have b14e7551 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b14e7550
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e7550 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7550
              have b14e7585 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e190 (σ x) (σ y)
                   have i₂ := b14e7551
                   grind)
                | exact superpose b14e7551 b14e190
                | exact resolve b14e190 b14e7551
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e190 b14e7551
              have b14e7622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e7585
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e7585
                | exact resolve b14e7585 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7585
              have b14e7623 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear b14e7622
              have b14e7665 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b14e671 y (σ x)
                   have i₂ := b14e7623
                   grind)
                | exact superpose b14e7623 b14e671
                | exact resolve b14e671 b14e7623
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e671 b14e7623
              have b14e7728 : y = (k y (τ (σ x))) := by
                first
                | (have r₁ := b14e7665
                   have r₂ := b14e29
                   grind)
                | exact resolve b14e7665 b14e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29 b14e7665
              have b14e7734 : y = (k y x) := by
                first
                | (have i₁ := b14e7728
                   have i₂ := b14e16 x
                   grind)
                | exact superpose b14e16 b14e7728
                | exact resolve b14e7728 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7728
              have b14e7760 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b14e20 y x
                   have i₂ := b14e7734
                   grind)
                | exact superpose b14e7734 b14e20
                | (have j0 := b14e20 y x
                   grind)
                | exact resolve b14e20 b14e7734
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7734
              have b14e7761 : y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b14e7760
              have b14e7765 : x = (M.op x y) := by
                first
                | (have r₁ := b14e7761
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e7761 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e7761
              have b14e7768 : False := by grind
              exact b14e7768
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e22 : x ≠ (M.op y x) := by grind
            have b15e23 : y = (M.op y x) := by grind
            have b15e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e22
              | exact resolve b15e22 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e14 X0 y x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e35 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e14 X0 x y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e41 : y = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b15e34 y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e34
              | exact resolve b15e34 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e67 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b15e35 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e35
              | exact resolve b15e35 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e68 : y = (M.op y y) := by
              first
              | (have i₁ := b15e35 y
                 have i₂ := b15e41
                 grind)
              | exact superpose b15e41 b15e35
              | exact resolve b15e35 b15e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35 b15e41
            have b15e74 : x = (M.op x y) := by
              first
              | (have i₁ := b15e67
                 have i₂ := b15e68
                 grind)
              | exact superpose b15e68 b15e67
              | exact resolve b15e67 b15e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e67 b15e68
            have b15e75 : x = y := by
              first
              | (have i₁ := b15e74
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e74
              | exact resolve b15e74 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e74
            have b15e76 : False := by grind
            exact b15e76
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e24 : y = (M.op y x) := by grind
              have b16e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e27 : y ≠ (M.op x y) := by grind
              have b16e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : x ≠ y := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e27
                | exact resolve b16e27 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e51 : y ≠ y ∨ x = y ∨ x = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x y
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e58 : x = y ∨ x = (k x y) := by grind
              clear b16e51
              have b16e60 : x = (k x y) := by
                first
                | (have r₁ := b16e58
                   have r₂ := b16e29
                   grind)
                | exact resolve b16e58 b16e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e29 b16e58
              have b16e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 X1 X0
                   have i₂ := b16e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b16e20 b16e21
                | (have j1 := b16e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b16e21 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e305 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b16e63 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e63
              have b16e6280 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e305 y x
                   have i₂ := b16e60
                   grind)
                | exact superpose b16e60 b16e305
                | (have j0 := b16e305 y x
                   grind)
                | exact resolve b16e305 b16e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e60 b16e305
              have b16e6295 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              clear b16e6280
              have b16e6310 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b16e6295
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e6295 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e6295
              have b16e6315 : False := by grind
              exact b16e6315
            · have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : x ≠ (M.op y x) := by grind
              have b17e24 : y = (M.op y x) := by grind
              have b17e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : x ≠ y := by
                first
                | (have i₁ := b17e23
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e23
                | exact resolve b17e23 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e42 : y ≠ y ∨ x = y ∨ x = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x y
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e47 : x = y ∨ x = (k x y) := by grind
              clear b17e42
              have b17e48 : x = (k x y) := by
                first
                | (have r₁ := b17e47
                   have r₂ := b17e29
                   grind)
                | exact resolve b17e47 b17e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e29 b17e47
              have b17e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 X0
                   have i₂ := b17e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e252 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b17e51 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e51
              have b17e4396 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e252 y x
                   have i₂ := b17e48
                   grind)
                | exact superpose b17e48 b17e252
                | (have j0 := b17e252 y x
                   grind)
                | exact resolve b17e252 b17e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e48 b17e252
              have b17e4403 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              clear b17e4396
              have b17e4414 : (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b17e4403
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e4403 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4403
              have b17e4419 : False := by grind
              exact b17e4419
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op y x) := by grind
          have b18e22 : y ≠ (M.op y x) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b18e16 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 (σ x) (σ y)
               grind)
            | (have r₁ := b18e16 (σ x) (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : (σ y) = (k (σ x) (σ y)) := by grind
          clear b18e27
          have b18e30 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b18e28
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e28
            | exact resolve b18e28 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e35 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e30
               grind)
            | exact superpose b18e30 b18e14
            | exact resolve b18e14 b18e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e36 : y = (k x y) := by
            first
            | (have i₁ := b18e35
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e35
            | exact resolve b18e35 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e58 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e36
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e36 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e62 : y = (M.op y x) ∨ x = (M.op y x) := by grind
          clear b18e58
          have b18e66 : x = (M.op y x) := by
            first
            | (have r₁ := b18e62
               have r₂ := b18e22
               grind)
            | exact resolve b18e62 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e62
          have b18e69 : False := by grind
          exact b18e69
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e23 : y ≠ (M.op y x) := by grind
            have b19e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e17
              | (have j0 := b19e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b19e17 (σ x) (σ y)
                 have r₂ := b19e24
                 grind)
              | exact resolve b19e17 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e31 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b19e30
            have b19e32 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e31
              | exact resolve b19e31 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e37 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e32
                 grind)
              | exact superpose b19e32 b19e15
              | exact resolve b19e15 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e38 : y = (k x y) := by
              first
              | (have i₁ := b19e37
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e37
              | exact resolve b19e37 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37
            have b19e57 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b19e38
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e38
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e38 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38
            have b19e61 : y = (M.op y x) ∨ x = (M.op y x) := by grind
            clear b19e57
            have b19e65 : x = (M.op y x) := by
              first
              | (have r₁ := b19e61
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e61 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e61
            have b19e68 : False := by grind
            exact b19e68
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e23 : y ≠ (M.op y x) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b20e28 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b20e27
            have b20e29 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e28
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e30 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e29
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : y = (k x y) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e73 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e31
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e31 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e75 : y = (M.op y x) ∨ x = (M.op y x) := by grind
            clear b20e73
            have b20e78 : x = (M.op y x) := by
              first
              | (have r₁ := b20e75
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e75 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e75
            have b20e81 : False := by grind
            exact b20e81
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op y x) := by grind
            have b21e23 : y ≠ (M.op y x) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e24
              | exact resolve b21e24 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e50 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b21e45
            have b21e51 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e50
                 have r₂ := b21e27
                 grind)
              | exact resolve b21e50 b21e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e27 b21e50
            have b21e52 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e51
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e51
              | exact resolve b21e51 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e51
            have b21e55 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e52
                 grind)
              | exact superpose b21e52 b21e15
              | exact resolve b21e15 b21e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e52
            have b21e56 : x = (k x y) := by
              first
              | (have i₁ := b21e55
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e55
              | exact resolve b21e55 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e55
            have b21e69 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e56
                 grind)
              | exact superpose b21e56 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e56
            have b21e70 : x = (M.op y x) ∨ y = (M.op y x) := by grind
            clear b21e69
            have b21e72 : y = (M.op y x) := by
              first
              | (have r₁ := b21e70
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e70 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e70
            have b21e74 : False := by grind
            exact b21e74
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : x ≠ (M.op y x) := by grind
              have b22e24 : y ≠ (M.op y x) := by grind
              have b22e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b22e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b22e25
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e25
                | exact resolve b22e25 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e53 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b22e48
              have b22e55 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e53
                   have r₂ := b22e30
                   grind)
                | exact resolve b22e53 b22e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e30 b22e53
              have b22e57 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e55
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e55
                | exact resolve b22e55 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e55
              have b22e67 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e57
                   grind)
                | exact superpose b22e57 b22e16
                | exact resolve b22e16 b22e57
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e57
              have b22e68 : x = (k x y) := by
                first
                | (have i₁ := b22e67
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e67
                | exact resolve b22e67 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e67
              have b22e80 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e68
                   grind)
                | exact superpose b22e68 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e68
              have b22e81 : x = (M.op y x) ∨ y = (M.op y x) := by grind
              clear b22e80
              have b22e83 : y = (M.op y x) := by
                first
                | (have r₁ := b22e81
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e81 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e81
              have b22e85 : False := by grind
              exact b22e85
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : x ≠ (M.op y x) := by grind
              have b23e24 : y ≠ (M.op y x) := by grind
              have b23e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b23e25
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e25
                | exact resolve b23e25 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e42 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e45 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b23e42
              have b23e46 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e45
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e45 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29 b23e45
              have b23e47 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e46
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e46
                | exact resolve b23e46 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e46
              have b23e50 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e47
                   grind)
                | exact superpose b23e47 b23e16
                | exact resolve b23e16 b23e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e47
              have b23e51 : x = (k x y) := by
                first
                | (have i₁ := b23e50
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e50
                | exact resolve b23e50 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e50
              have b23e61 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e51
                   grind)
                | exact superpose b23e51 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e51
              have b23e62 : x = (M.op y x) ∨ y = (M.op y x) := by grind
              clear b23e61
              have b23e64 : y = (M.op y x) := by
                first
                | (have r₁ := b23e62
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e62 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e62
              have b23e66 : False := by grind
              exact b23e66
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e23 : y ≠ (M.op y x) := by grind
            have b24e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e32 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
              intro X0
              first
              | (have i₁ := b24e14 X0 x y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
                 have i₂ := b24e14 X0 X2 X3
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e37 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b24e32 x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e32
              | exact resolve b24e32 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e88 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e33 X0 X0 x x
                 have i₂ := b24e14 X0 x x
                 grind)
              | exact superpose b24e14 b24e33
              | exact resolve b24e33 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e102 : y = (M.op y y) := by
              first
              | (have i₁ := b24e32 y
                 have i₂ := b24e88 y
                 grind)
              | exact superpose b24e88 b24e32
              | exact resolve b24e32 b24e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32 b24e88
            have b24e132 : x = (M.op x y) := by
              first
              | (have i₁ := b24e37
                 have i₂ := b24e102
                 grind)
              | exact superpose b24e102 b24e37
              | exact resolve b24e37 b24e102
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e37
            have b24e144 : x = y := by
              first
              | (have i₁ := b24e132
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e132
              | exact resolve b24e132 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e132
            have b24e176 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e144
                 grind)
              | exact superpose b24e144 b24e23
              | exact resolve b24e23 b24e144
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e144
            have b24e184 : False := by grind
            exact b24e184
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e27 : y ≠ (M.op x y) := by grind
              have b25e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : x ≠ y := by
                first
                | (have i₁ := b25e27
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e27
                | exact resolve b25e27 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e30 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e22
                | exact resolve b25e22 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e43 : x ≠ x ∨ x = y ∨ y = (k y x) := by
                first
                | (have i₁ := b25e19 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e19
                | (have j0 := b25e19 y x
                   grind)
                | (have r₁ := b25e19 y x
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e19 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e48 : x = y ∨ y = (k y x) := by grind
              clear b25e43
              have b25e49 : y = (k y x) := by
                first
                | (have r₁ := b25e48
                   have r₂ := b25e29
                   grind)
                | exact resolve b25e48 b25e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e29 b25e48
              have b25e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b25e253 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b25e52 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e52
              have b25e4397 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e253 x y
                   have i₂ := b25e49
                   grind)
                | exact superpose b25e49 b25e253
                | (have j0 := b25e253 x y
                   grind)
                | exact resolve b25e253 b25e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e253
              have b25e4402 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              clear b25e4397
              have b25e4414 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b25e4402
                   have r₂ := b25e30
                   grind)
                | exact resolve b25e4402 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4402
              have b25e4426 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b25e30
                   have i₂ := b25e4414
                   grind)
                | exact superpose b25e4414 b25e30
                | exact resolve b25e30 b25e4414
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30
              have b25e4429 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b25e18 (σ y) (σ x)
                   have i₂ := b25e4414
                   grind)
                | exact superpose b25e4414 b25e18
                | (have j0 := b25e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b25e18 (σ y) (σ x)
                   have r₂ := b25e4414
                   grind)
                | exact resolve b25e18 b25e4414
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4414
              have b25e4474 : (σ x) = (k (σ y) (σ x)) := by grind
              clear b25e4429
              have b25e4496 : (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b25e4474
                   have i₂ := b25e21 y x
                   grind)
                | exact superpose b25e21 b25e4474
                | exact resolve b25e4474 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e4474
              have b25e4501 : (σ x) = (σ y) := by
                first
                | (have i₁ := b25e4496
                   have i₂ := b25e49
                   grind)
                | exact superpose b25e49 b25e4496
                | exact resolve b25e4496 b25e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e49 b25e4496
              have b25e4502 : False := by grind
              exact b25e4502
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e27 : y ≠ (M.op x y) := by grind
              have b26e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e31 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
                   have i₂ := b26e15 X0 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k X0 (τ X1))
                   have i₂ := b26e30 X1 X0
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30
              have b26e49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b26e65 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e31 X0 X0 x x
                   have i₂ := b26e15 X0 x x
                   grind)
                | exact superpose b26e15 b26e31
                | exact resolve b26e31 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e31
              have b26e77 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X1 X0 (M.op X0 X0)
                   have i₂ := b26e65 X0
                   grind)
                | exact superpose b26e65 b26e15
                | exact resolve b26e15 b26e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e65
              have b26e172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e49 x y
                   grind)
                | exact superpose b26e49 b26e22
                | (have j1 := b26e49 x y
                   grind)
                | exact resolve b26e22 b26e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49
              have b26e229 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e77 X0 (M.op X1 X0)
                   have i₂ := b26e15 X0 X1 X0
                   grind)
                | exact superpose b26e15 b26e77
                | exact resolve b26e77 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e77
              have b26e279 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 (M.op X0 X1)
                   have i₂ := b26e229 X1 X0
                   grind)
                | exact superpose b26e229 b26e18
                | (have j0 := b26e18 X1 X0
                   grind)
                | exact resolve b26e18 b26e229
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e280 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e19 X0 (M.op X1 X0)
                   have i₂ := b26e229 X0 X1
                   grind)
                | exact superpose b26e229 b26e19
                | (have j0 := b26e19 X1 X0
                   grind)
                | (have r₁ := b26e19 X0 (M.op X1 X0)
                   have r₂ := b26e229 X0 X1
                   grind)
                | exact resolve b26e19 b26e229
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e229
              have b26e294 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e280 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e280
              have b26e361 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e45 X0 (M.op X1 (σ X0))
                   have i₂ := b26e294 X1 (σ X0)
                   grind)
                | exact superpose b26e294 b26e45
                | (have j1 := b26e294 X1 (σ X0)
                   grind)
                | exact resolve b26e45 b26e294
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e45 b26e294
              have b26e366 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e361 X0 X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e361
                | (have j0 := b26e361 X0 X1
                   grind)
                | exact resolve b26e361 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e361
              have b26e2573 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e172
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e172
                | (have j1 := b26e20 (σ y) (σ x)
                   grind)
                | exact resolve b26e172 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e172
              have b26e2574 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
              clear b26e2573
              have b26e2575 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b26e2574
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e2574 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2574
              have b26e2576 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e2575
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e2575 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2575
              have b26e2581 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e18 (σ y) (σ x)
                   have i₂ := b26e2576
                   grind)
                | exact superpose b26e2576 b26e18
                | (have j0 := b26e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b26e18 (σ y) (σ x)
                   have r₂ := b26e2576
                   grind)
                | exact resolve b26e18 b26e2576
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2576
              have b26e2626 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
              clear b26e2581
              have b26e2645 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b26e2626
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e2626
                | exact resolve b26e2626 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2626
              have b26e2955 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b26e279 (σ x) (σ y)
                   have i₂ := b26e2645
                   grind)
                | exact superpose b26e2645 b26e279
                | exact resolve b26e279 b26e2645
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e279
              have b26e2961 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b26e2955
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e2955
                | exact resolve b26e2955 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2955
              have b26e2962 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by grind
              clear b26e2961
              have b26e4339 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b26e366 y (σ x)
                   have i₂ := b26e2645
                   grind)
                | exact superpose b26e2645 b26e366
                | exact resolve b26e366 b26e2645
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e366 b26e2645
              have b26e4384 : y = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have r₁ := b26e4339
                   have r₂ := b26e2962
                   grind)
                | exact resolve b26e4339 b26e2962
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2962 b26e4339
              have b26e4393 : (σ x) = (σ (k y x)) ∨ y = (k y x) := by
                first
                | (have i₁ := b26e4384
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e4384
                | exact resolve b26e4384 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4384
              have b26e4521 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e4393
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e4393
                | (have j1 := b26e20 y x
                   grind)
                | exact resolve b26e4393 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4393
              have b26e4561 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b26e4521
              have b26e4579 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b26e4561
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e4561 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4561
              have b26e4580 : (σ (M.op x y)) = (σ x) := by
                first
                | (have r₁ := b26e4579
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e4579 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4579
              have b26e4678 : (M.op x y) = (τ (σ x)) := by
                first
                | (have i₁ := b26e16 (M.op x y)
                   have i₂ := b26e4580
                   grind)
                | exact superpose b26e4580 b26e16
                | exact resolve b26e16 b26e4580
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4580
              have b26e4725 : x = (M.op x y) := by
                first
                | (have i₁ := b26e4678
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e4678
                | exact resolve b26e4678 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4678
              have b26e4726 : False := by grind
              exact b26e4726
