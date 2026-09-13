import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1323`: `x = y ◇ (((y ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1323 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1323 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1323.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
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
      have b0e57 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e59 : False := by grind
      exact b0e59
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
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
               have i₂ := b4e13 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e88 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0)
               have i₂ := b4e32 X1 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e134 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e50 x y
               grind)
            | exact superpose b4e50 b4e20
            | (have j1 := b4e50 x y
               grind)
            | exact resolve b4e20 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e139 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e134
               have r₂ := b4e23
               grind)
            | exact resolve b4e134 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e170 : y = (M.op (M.op x x) (M.op x y)) := by
            first
            | (have i₁ := b4e88 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e88
            | exact resolve b4e88 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e389 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e139
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e139
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e139
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e139
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e139 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139
          have b4e390 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e389
          have b4e391 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e390
               have r₂ := b4e21
               grind)
            | exact resolve b4e390 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e390
          have b4e394 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e391
               grind)
            | exact superpose b4e391 b4e20
            | exact resolve b4e20 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e397 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e391
               grind)
            | exact superpose b4e391 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e391
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e391
               grind)
            | exact resolve b4e17 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e391
          have b4e398 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e397
          have b4e399 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e398
               have r₂ := b4e23
               grind)
            | exact resolve b4e398 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e398
          have b4e403 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e399
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e399
            | exact resolve b4e399 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e399
          have b4e476 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e403
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e403
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e403 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e403
          have b4e496 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e476
          have b4e511 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e496
               have r₂ := b4e394
               grind)
            | exact resolve b4e496 b4e394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394 b4e496
          have b4e512 : x = (M.op x y) := by
            first
            | (have r₁ := b4e511
               have r₂ := b4e21
               grind)
            | exact resolve b4e511 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e511
          have b4e552 : y = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b4e170
               have i₂ := b4e512
               grind)
            | exact superpose b4e512 b4e170
            | exact resolve b4e170 b4e512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e622 : (M.op x x) = (M.op (M.op x x) (M.op x y)) := by
            first
            | (have i₁ := b4e88 x (M.op x x)
               have i₂ := b4e552
               grind)
            | exact superpose b4e552 b4e88
            | exact resolve b4e88 b4e552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e552
          have b4e624 : y = (M.op x x) := by
            first
            | (have i₁ := b4e622
               have i₂ := b4e170
               grind)
            | exact superpose b4e170 b4e622
            | exact resolve b4e622 b4e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e170 b4e622
          have b4e677 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b4e88 x x
               have i₂ := b4e624
               grind)
            | exact superpose b4e624 b4e88
            | exact resolve b4e88 b4e624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88 b4e624
          have b4e678 : x = (M.op y x) := by
            first
            | (have i₁ := b4e677
               have i₂ := b4e512
               grind)
            | exact superpose b4e512 b4e677
            | exact resolve b4e677 b4e512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e512 b4e677
          have b4e682 : x = y := by
            first
            | (have i₁ := b4e678
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e678
            | exact resolve b4e678 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e678
          have b4e684 : False := by grind
          exact b4e684
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e40 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e42 : x = y ∨ y = (k x y) := by grind
          clear b5e40
          have b5e43 : y = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e21
               grind)
            | exact resolve b5e42 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e132 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e46 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e604 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e132 y x
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e132
            | (have j0 := b5e132 y x
               grind)
            | exact resolve b5e132 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e132
          have b5e611 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e604
          have b5e615 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e611
               have r₂ := b5e24
               grind)
            | exact resolve b5e611 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e611
          have b5e619 : False := by grind
          exact b5e619
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e40
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
          have b7e58 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
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
          have b7e59 : y = (M.op y x) ∨ x = y := by grind
          clear b7e58
          have b7e61 : x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e22
               grind)
            | exact resolve b7e59 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e63 : False := by grind
          exact b7e63
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e103 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e108 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e103
               have r₂ := b8e23
               grind)
            | exact resolve b8e103 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e385 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e108
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e108
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e108
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e108
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e108 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e386 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e385
          have b8e387 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e386
               have r₂ := b8e21
               grind)
            | exact resolve b8e386 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e386
          have b8e389 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e387
               grind)
            | exact superpose b8e387 b8e20
            | exact resolve b8e20 b8e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e392 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e387
               grind)
            | exact superpose b8e387 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e387
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e387
               grind)
            | exact resolve b8e17 b8e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e387
          have b8e393 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e392
          have b8e394 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e393
               have r₂ := b8e23
               grind)
            | exact resolve b8e393 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e393
          have b8e397 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e394
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e394
            | exact resolve b8e394 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e394
          have b8e469 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e397
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e397
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e397 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e397
          have b8e489 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e469
          have b8e504 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e489
               have r₂ := b8e389
               grind)
            | exact resolve b8e489 b8e389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e389 b8e489
          have b8e505 : x = (M.op x y) := by
            first
            | (have r₁ := b8e504
               have r₂ := b8e21
               grind)
            | exact resolve b8e504 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e546 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e505
               grind)
            | exact superpose b8e505 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e505
               grind)
            | exact resolve b8e17 b8e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e547 : x = y ∨ x = (k y x) := by grind
          clear b8e546
          have b8e548 : x = (k y x) := by
            first
            | (have r₁ := b8e547
               have r₂ := b8e21
               grind)
            | exact resolve b8e547 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e547
          have b8e577 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e108
               have i₂ := b8e548
               grind)
            | exact superpose b8e548 b8e108
            | exact resolve b8e108 b8e548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108 b8e548
          have b8e581 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e577
               have i₂ := b8e505
               grind)
            | exact superpose b8e505 b8e577
            | exact resolve b8e577 b8e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e577
          have b8e582 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e581
          have b8e610 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e582
               grind)
            | exact superpose b8e582 b8e20
            | exact resolve b8e20 b8e582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e582
          have b8e617 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e610
               have i₂ := b8e505
               grind)
            | exact superpose b8e505 b8e610
            | exact resolve b8e610 b8e505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e505 b8e610
          have b8e618 : False := by grind
          exact b8e618

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e45 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e47 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e47
      have b0e50 : (M.op x x) = (k x y) := by grind
      clear b0e45
      have b0e51 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e49
        | exact resolve b0e49 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e51
           have i₂ := b0e50
           grind)
        | exact superpose b0e50 b0e51
        | exact resolve b0e51 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e51
      have b0e53 : False := by grind
      exact b0e53
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : False := by grind
        exact b1e25
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : (M.op x x) = (k x y) := by grind
        clear b2e52
        have b2e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e54 (σ X0)
             grind)
          | exact superpose b2e54 b2e18
          | exact resolve b2e18 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e57 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e57
          | exact resolve b2e57 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e57
        have b2e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e72 X0 X1
             have i₂ := b2e64 X0
             grind)
          | exact superpose b2e64 b2e72
          | (have j0 := b2e72 X0 X1
             grind)
          | exact resolve b2e72 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e615 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e88 x y
             grind)
          | exact superpose b2e88 b2e21
          | (have j1 := b2e88 x y
             grind)
          | exact resolve b2e21 b2e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88
        have b2e670 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e615
             have r₂ := b2e24
             grind)
          | exact resolve b2e615 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e615
        have b2e683 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e670
             have r₂ := b2e22
             grind)
          | exact resolve b2e670 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e670
        have b2e689 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e683
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e683
          | exact resolve b2e683 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e683
        have b2e691 : False := by grind
        exact b2e691
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e55 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e53
        have b6e56 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e55
          | exact resolve b6e55 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e93 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e24
          | exact resolve b6e24 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e56
        have b6e127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e93
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e93
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e93
             have r₂ := b6e17 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e93
             have r₂ := b6e17 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e93 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93
        have b6e128 : (M.op x y) = (M.op x x) ∨ x = y := by grind
        clear b6e127
        have b6e129 : x = y := by
          first
          | (have r₁ := b6e128
             have r₂ := b6e20
             grind)
          | exact resolve b6e128 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e130 : False := by grind
        exact b6e130
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : False := by grind
          exact b7e27
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
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
          have b8e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e44 (σ X0)
               grind)
            | exact superpose b8e44 b8e19
            | exact resolve b8e19 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e46 X0
               have i₂ := b8e44 X0
               grind)
            | exact superpose b8e44 b8e46
            | exact resolve b8e46 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44 b8e46
          have b8e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e65 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57 X0 X1
               have i₂ := b8e51 X0
               grind)
            | exact superpose b8e51 b8e57
            | (have j0 := b8e57 X0 X1
               grind)
            | exact resolve b8e57 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e173 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e176 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e173 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e173 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e173 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e173 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e173 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e245 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e176 (τ X0) X1
               grind)
            | exact superpose b8e176 b8e26
            | (have j1 := b8e176 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e176
          have b8e570 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e72 x y
               grind)
            | exact superpose b8e72 b8e20
            | (have j1 := b8e72 x y
               grind)
            | exact resolve b8e20 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e630 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e570
               have r₂ := b8e24
               grind)
            | exact resolve b8e570 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e570
          have b8e1236 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e245 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e245
            | exact resolve b8e245 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e245
          have b8e1273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1236 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1236
            | (have j0 := b8e1236 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e1236 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1236
          have b8e2392 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e630
               have i₂ := b8e1273 x y
               grind)
            | exact superpose b8e1273 b8e630
            | (have j1 := b8e1273 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b8e630
               have r₂ := b8e1273 x y
               grind)
            | (have r₁ := b8e630
               have r₂ := b8e1273 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e630
               have r₂ := b8e1273 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e630 b8e1273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e630 b8e1273
          have b8e2393 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b8e2392
          have b8e2399 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e2393
               have r₂ := b8e22
               grind)
            | exact resolve b8e2393 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2393
          have b8e2406 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e2399
               grind)
            | exact superpose b8e2399 b8e23
            | exact resolve b8e23 b8e2399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2399
          have b8e2444 : False := by grind
          exact b8e2444

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e41 : (M.op x y) = (k x y) := by grind
      have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e40
        | exact resolve b0e40 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e44 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e43
        | exact resolve b0e43 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e43
      have b0e45 : False := by grind
      exact b0e45
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b1e39 : (M.op x y) = (k x y) := by grind
        have b1e68 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e81 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e68
             have r₂ := b1e21
             grind)
          | exact resolve b1e68 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e82 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e81
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e81
          | exact resolve b1e81 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81
        have b1e83 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e82
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e82
          | exact resolve b1e82 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e82
        have b1e84 : False := by grind
        exact b1e84
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e52 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e52 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e52 b2e71
          | (have j1 := b2e52 X1 X0
             grind)
          | exact resolve b2e71 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e71
        have b2e457 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e428 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e428
        have b2e3599 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e457 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e457
        have b2e3600 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e3599 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3599
        have b2e3622 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e3600 (σ X0)
             grind)
          | exact superpose b2e3600 b2e18
          | exact resolve b2e18 b2e3600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3629 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3622 X0
             have i₂ := b2e3600 X0
             grind)
          | exact superpose b2e3600 b2e3622
          | exact resolve b2e3622 b2e3600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3600 b2e3622
        have b2e3984 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e3629 x
             grind)
          | exact superpose b2e3629 b2e21
          | exact resolve b2e21 b2e3629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3629
        have b2e4045 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e3984
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3984
          | exact resolve b2e3984 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3984
        have b2e4046 : False := by grind
        exact b2e4046
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b3e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e38
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e38
          | exact resolve b3e38 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e67 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e79 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e67
             have r₂ := b3e20
             grind)
          | exact resolve b3e67 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e115 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e19
          | exact resolve b3e19 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e120 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e79
             grind)
          | exact superpose b3e79 b3e115
          | exact resolve b3e115 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79 b3e115
        have b3e121 : False := by grind
        exact b3e121
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
          have b4e77 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e78 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e90 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e78
               have r₂ := b4e21
               grind)
            | exact resolve b4e78 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e91 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e77
               have r₂ := b4e23
               grind)
            | exact resolve b4e77 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e92 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e91
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e91
            | exact resolve b4e91 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e93 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e92
               have i₂ := b4e90
               grind)
            | exact superpose b4e90 b4e92
            | exact resolve b4e92 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90 b4e92
          have b4e94 : False := by grind
          exact b4e94
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e371 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e59 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e59 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e59 b5e79
            | (have j1 := b5e59 X1 X0
               grind)
            | exact resolve b5e79 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e79
          have b5e396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e371 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e371
          have b5e3434 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e396 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e396
          have b5e3435 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e3434 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3434
          have b5e3457 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e3435 (σ X0)
               grind)
            | exact superpose b5e3435 b5e19
            | exact resolve b5e19 b5e3435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e3457 X0
               have i₂ := b5e3435 X0
               grind)
            | exact superpose b5e3435 b5e3457
            | exact resolve b5e3457 b5e3435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3435 b5e3457
          have b5e3843 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3464 y
               grind)
            | exact superpose b5e3464 b5e24
            | exact resolve b5e24 b5e3464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3464
          have b5e3898 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e3843
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3843
            | exact resolve b5e3843 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3843
          have b5e3899 : False := by grind
          exact b5e3899
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e29 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
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
        have b6e30 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X1 X0) X0 (M.op X1 x)
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b6e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b6e71 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e80 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e81 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e80 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e71 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e92 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (k x y))) := by
          first
          | (have i₁ := b6e29 (σ x)
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e29
          | exact resolve b6e29 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e100 : (σ x) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e92
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e92
          | exact resolve b6e92 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e104 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e30 (σ x) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e30
          | exact resolve b6e30 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e138 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b6e31 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e31
          | exact resolve b6e31 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e155 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b6e138
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e138
          | exact resolve b6e138 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e138
        have b6e177 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e100
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e100
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e100 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100
        have b6e184 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e177
             have r₂ := b6e20
             grind)
          | exact resolve b6e177 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e177
        have b6e185 : (σ x) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have r₁ := b6e184
             have r₂ := b6e21
             grind)
          | exact resolve b6e184 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184
        have b6e198 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e155
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e155
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e155 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e155
        have b6e205 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e198
             have r₂ := b6e20
             grind)
          | exact resolve b6e198 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e198
        have b6e206 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
          first
          | (have r₁ := b6e205
             have r₂ := b6e21
             grind)
          | exact resolve b6e205 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e205
        have b6e487 : (σ (M.op y x)) = (M.op (M.op (σ y) (σ (M.op y x))) (σ y)) := by
          first
          | (have i₁ := b6e104 (σ (M.op y x))
             have i₂ := b6e206
             grind)
          | exact superpose b6e206 b6e104
          | exact resolve b6e104 b6e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104 b6e206
        have b6e511 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e487
             have i₂ := b6e185
             grind)
          | exact superpose b6e185 b6e487
          | exact resolve b6e487 b6e185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e185 b6e487
        have b6e1460 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64
          | exact resolve b6e64 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e1692 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1460
        have b6e3432 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1692
             grind)
          | exact superpose b6e1692 b6e13
          | exact resolve b6e13 b6e1692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1692
        have b6e3446 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3432
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3432
          | exact resolve b6e3432 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3432
        have b6e3644 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e83 x x
             have i₂ := b6e3446
             grind)
          | exact superpose b6e3446 b6e83
          | (have j0 := b6e83 x y
             grind)
          | exact resolve b6e83 b6e3446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e3645 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3644
        have b6e3655 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3645
             have r₂ := b6e20
             grind)
          | exact resolve b6e3645 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3645
        have b6e3774 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e81 x
             have i₂ := b6e3655
             grind)
          | exact superpose b6e3655 b6e81
          | exact resolve b6e81 b6e3655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e3655
        have b6e4034 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3446
             have i₂ := b6e3774
             grind)
          | exact superpose b6e3774 b6e3446
          | exact resolve b6e3446 b6e3774
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3446 b6e3774
        have b6e4037 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e4034
        have b6e4039 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e4037
             have r₂ := b6e20
             grind)
          | exact resolve b6e4037 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4037
        have b6e4117 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e4039
             grind)
          | exact superpose b6e4039 b6e19
          | exact resolve b6e19 b6e4039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4131 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e511
             have i₂ := b6e4039
             grind)
          | exact superpose b6e4039 b6e511
          | exact resolve b6e511 b6e4039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e511
        have b6e4134 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e4039
             grind)
          | exact superpose b6e4039 b6e13
          | exact resolve b6e13 b6e4039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4151 : x = y := by
          first
          | (have i₁ := b6e4134
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4134
          | exact resolve b6e4134 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4134
        have b6e4153 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e4131
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4131
          | exact resolve b6e4131 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4131
        have b6e4162 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4117
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4117
          | exact resolve b6e4117 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4117
        have b6e4168 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4153
             have i₂ := b6e4151
             grind)
          | exact superpose b6e4151 b6e4153
          | exact resolve b6e4153 b6e4151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4153
        have b6e4174 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4162
             have i₂ := b6e4039
             grind)
          | exact superpose b6e4039 b6e4162
          | exact resolve b6e4162 b6e4039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4039 b6e4162
        have b6e4184 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4174
             have i₂ := b6e4151
             grind)
          | exact superpose b6e4151 b6e4174
          | exact resolve b6e4174 b6e4151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4151 b6e4174
        have b6e4186 : False := by grind
        exact b6e4186
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e35 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
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
          have b7e36 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X1 X0) X0 (M.op X1 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b7e48 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e92 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e93 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e92 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e95 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e105 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ (k y x))) := by
            first
            | (have i₁ := b7e35 (σ y)
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e35
            | exact resolve b7e35 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e113 : (σ y) = (M.op (σ x) (σ (k y x))) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e105
            | exact resolve b7e105 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e120 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e36 (σ y) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e147 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e37 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e165 : (σ x) = (M.op (σ (k y x)) (σ y)) := by
            first
            | (have i₁ := b7e147
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e147
            | exact resolve b7e147 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e147
          have b7e187 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e113
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e113
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e113 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e194 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e187
               have r₂ := b7e22
               grind)
            | exact resolve b7e187 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e187
          have b7e195 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have r₁ := b7e194
               have r₂ := b7e21
               grind)
            | exact resolve b7e194 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e194
          have b7e208 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e165
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e165
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e165 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e165
          have b7e215 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e208
               have r₂ := b7e22
               grind)
            | exact resolve b7e208 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e208
          have b7e216 : (σ x) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have r₁ := b7e215
               have r₂ := b7e21
               grind)
            | exact resolve b7e215 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e215
          have b7e400 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) := by
            first
            | (have i₁ := b7e120 (σ (M.op x y))
               have i₂ := b7e216
               grind)
            | exact superpose b7e216 b7e120
            | exact resolve b7e120 b7e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120 b7e216
          have b7e423 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e400
               have i₂ := b7e195
               grind)
            | exact superpose b7e195 b7e400
            | exact resolve b7e400 b7e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e195 b7e400
          have b7e1491 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e70 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e70
            | exact resolve b7e70 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e1719 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1491
          have b7e2025 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1719
               grind)
            | exact superpose b7e1719 b7e14
            | exact resolve b7e14 b7e1719
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1719
          have b7e2039 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2025
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2025
            | exact resolve b7e2025 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2025
          have b7e2285 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e95 y y
               have i₂ := b7e2039
               grind)
            | exact superpose b7e2039 b7e95
            | (have j0 := b7e95 y x
               grind)
            | exact resolve b7e95 b7e2039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e2286 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2285
          have b7e2296 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2286
               have r₂ := b7e22
               grind)
            | exact resolve b7e2286 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2286
          have b7e2556 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e93 y
               have i₂ := b7e2296
               grind)
            | exact superpose b7e2296 b7e93
            | exact resolve b7e93 b7e2296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e2296
          have b7e3452 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2039
               have i₂ := b7e2556
               grind)
            | exact superpose b7e2556 b7e2039
            | exact resolve b7e2039 b7e2556
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2039 b7e2556
          have b7e3455 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3452
          have b7e3457 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3455
               have r₂ := b7e22
               grind)
            | exact resolve b7e3455 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3455
          have b7e3725 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e3457
               grind)
            | exact superpose b7e3457 b7e20
            | exact resolve b7e20 b7e3457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3739 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e423
               have i₂ := b7e3457
               grind)
            | exact superpose b7e3457 b7e423
            | exact resolve b7e423 b7e3457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e423 b7e3457
          have b7e3762 : False := by grind
          exact b7e3762
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
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
          have b8e319 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e63 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e320 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e319
               have r₂ := b8e23
               grind)
            | exact resolve b8e319 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319
          have b8e321 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e320
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e320
            | exact resolve b8e320 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e320
          have b8e322 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e321
               grind)
            | exact superpose b8e321 b8e20
            | exact resolve b8e20 b8e321
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e321
          have b8e412 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e322
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e322
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e322 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322
          have b8e418 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e412
          have b8e421 : y = (M.op x x) := by
            first
            | (have r₁ := b8e418
               have r₂ := b8e22
               grind)
            | exact resolve b8e418 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e418
          have b8e422 : False := by grind
          exact b8e422

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e80 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e232 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e81 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e81
        | exact resolve b0e81 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e233 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e81 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e81
        | exact resolve b0e81 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e236 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e232
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e232
        | exact resolve b0e232 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232
      have b0e237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e236
           have i₂ := b0e233
           grind)
        | exact superpose b0e233 b0e236
        | exact resolve b0e236 b0e233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233 b0e236
      have b0e238 : False := by grind
      exact b0e238
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e38 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e77 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e115 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e19
          | exact resolve b1e19 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e241 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e78 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e78
          | exact resolve b1e78 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e247 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e115
             have i₂ := b1e241
             grind)
          | exact superpose b1e241 b1e115
          | exact resolve b1e115 b1e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e115 b1e241
        have b1e249 : False := by grind
        exact b1e249
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e423 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e52 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e52 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e52 b2e71
          | (have j1 := b2e52 X1 X0
             grind)
          | exact resolve b2e71 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e71
        have b2e452 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e423 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e423
        have b2e3601 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e452 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e452
        have b2e3602 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e3601 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3601
        have b2e3624 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e3602 (σ X0)
             grind)
          | exact superpose b2e3602 b2e18
          | exact resolve b2e18 b2e3602
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3631 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3624 X0
             have i₂ := b2e3602 X0
             grind)
          | exact superpose b2e3602 b2e3624
          | exact resolve b2e3624 b2e3602
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3602 b2e3624
        have b2e3986 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e3631 x
             grind)
          | exact superpose b2e3631 b2e21
          | exact resolve b2e21 b2e3631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3631
        have b2e4047 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e3986
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3986
          | exact resolve b2e3986 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3986
        have b2e4048 : False := by grind
        exact b2e4048
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e39 : (M.op x y) = (k y x) := by grind
        have b3e66 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e80 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e66
          | exact resolve b3e66 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e81 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e80
          | exact resolve b3e80 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e82 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e81
             have r₂ := b3e19
             grind)
          | exact resolve b3e81 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e92 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e82
        have b3e93 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e92
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e92
          | exact resolve b3e92 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e94 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e93
          | exact resolve b3e93 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e93
        have b3e95 : False := by grind
        exact b3e95
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e45 : (M.op x y) = (k y x) := by grind
          have b4e47 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e44
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e44
            | exact resolve b4e44 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e47
            | exact resolve b4e47 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e47
          have b4e49 : False := by grind
          exact b4e49
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e365 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e59 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e59 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e59 b5e79
            | (have j1 := b5e59 X1 X0
               grind)
            | exact resolve b5e79 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e79
          have b5e390 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e365 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e365
          have b5e3426 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e390 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e390
          have b5e3427 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e3426 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3426
          have b5e3447 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e3427 (σ X0)
               grind)
            | exact superpose b5e3427 b5e19
            | exact resolve b5e19 b5e3427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3454 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e3447 X0
               have i₂ := b5e3427 X0
               grind)
            | exact superpose b5e3427 b5e3447
            | exact resolve b5e3447 b5e3427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3427 b5e3447
          have b5e3833 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3454 y
               grind)
            | exact superpose b5e3454 b5e24
            | exact resolve b5e24 b5e3454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3454
          have b5e3888 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e3833
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3833
            | exact resolve b5e3833 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3833
          have b5e3889 : False := by grind
          exact b5e3889
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e29 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
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
        have b6e30 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X1 X0) X0 (M.op X1 x)
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e70 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e82 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e115 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e30 (σ x) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e30
          | exact resolve b6e30 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e152 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b6e31 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e31
          | exact resolve b6e31 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e80 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e80
          | exact resolve b6e80 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e174 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e168
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e168
          | exact resolve b6e168 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e168
        have b6e187 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (k y x))) := by
          first
          | (have i₁ := b6e29 (σ x)
             have i₂ := b6e174
             grind)
          | exact superpose b6e174 b6e29
          | exact resolve b6e29 b6e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e193 : (σ x) = (M.op (σ y) (σ (k y x))) := by
          first
          | (have i₁ := b6e187
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e187
          | exact resolve b6e187 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e187
        have b6e321 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e193
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e193
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e193 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e193
        have b6e329 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e321
             have r₂ := b6e21
             grind)
          | exact resolve b6e321 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e321
        have b6e331 : (σ x) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have r₁ := b6e329
             have r₂ := b6e20
             grind)
          | exact resolve b6e329 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e329
        have b6e1362 : (σ y) = (M.op (σ (k y x)) (σ x)) := by
          first
          | (have i₁ := b6e152
             have i₂ := b6e174
             grind)
          | exact superpose b6e174 b6e152
          | exact resolve b6e152 b6e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e152 b6e174
        have b6e1403 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64
          | exact resolve b6e64 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e1633 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1403
        have b6e1693 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e1362
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e1362
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e1362 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1362
        have b6e1722 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e1693
             have r₂ := b6e21
             grind)
          | exact resolve b6e1693 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1693
        have b6e1725 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
          first
          | (have r₁ := b6e1722
             have r₂ := b6e20
             grind)
          | exact resolve b6e1722 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1722
        have b6e1938 : (σ (M.op y x)) = (M.op (M.op (σ y) (σ (M.op y x))) (σ y)) := by
          first
          | (have i₁ := b6e115 (σ (M.op y x))
             have i₂ := b6e1725
             grind)
          | exact superpose b6e1725 b6e115
          | exact resolve b6e115 b6e1725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e1725
        have b6e1956 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e1938
             have i₂ := b6e331
             grind)
          | exact superpose b6e331 b6e1938
          | exact resolve b6e1938 b6e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e331 b6e1938
        have b6e3399 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1633
             grind)
          | exact superpose b6e1633 b6e13
          | exact resolve b6e13 b6e1633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1633
        have b6e3413 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3399
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3399
          | exact resolve b6e3399 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3399
        have b6e3437 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e82 x x
             have i₂ := b6e3413
             grind)
          | exact superpose b6e3413 b6e82
          | (have j0 := b6e82 x y
             grind)
          | exact resolve b6e82 b6e3413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e3438 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3437
        have b6e3448 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3438
             have r₂ := b6e20
             grind)
          | exact resolve b6e3438 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3438
        have b6e3649 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e80 x
             have i₂ := b6e3448
             grind)
          | exact superpose b6e3448 b6e80
          | exact resolve b6e80 b6e3448
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80 b6e3448
        have b6e3919 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3413
             have i₂ := b6e3649
             grind)
          | exact superpose b6e3649 b6e3413
          | exact resolve b6e3413 b6e3649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3413 b6e3649
        have b6e3922 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3919
        have b6e3924 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3922
             have r₂ := b6e20
             grind)
          | exact resolve b6e3922 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3922
        have b6e3973 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3924
             grind)
          | exact superpose b6e3924 b6e19
          | exact resolve b6e19 b6e3924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3988 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e1956
             have i₂ := b6e3924
             grind)
          | exact superpose b6e3924 b6e1956
          | exact resolve b6e1956 b6e3924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1956
        have b6e3989 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3924
             grind)
          | exact superpose b6e3924 b6e13
          | exact resolve b6e13 b6e3924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4006 : x = y := by
          first
          | (have i₁ := b6e3989
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3989
          | exact resolve b6e3989 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3989
        have b6e4007 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e3988
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3988
          | exact resolve b6e3988 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3988
        have b6e4016 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e3973
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3973
          | exact resolve b6e3973 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3973
        have b6e4021 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4007
             have i₂ := b6e4006
             grind)
          | exact superpose b6e4006 b6e4007
          | exact resolve b6e4007 b6e4006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4007
        have b6e4028 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4016
             have i₂ := b6e3924
             grind)
          | exact superpose b6e3924 b6e4016
          | exact resolve b6e4016 b6e3924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3924 b6e4016
        have b6e4037 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4028
             have i₂ := b6e4006
             grind)
          | exact superpose b6e4006 b6e4028
          | exact resolve b6e4028 b6e4006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4006 b6e4028
        have b6e4039 : False := by grind
        exact b6e4039
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b7e35 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
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
          have b7e36 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X1 X0) X0 (M.op X1 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e77 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          have b7e78 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e88 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e87 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e91 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e23
               grind)
            | exact resolve b7e77 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e92 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e91
            | exact resolve b7e91 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e108 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ (k x y))) := by
            first
            | (have i₁ := b7e35 (σ y)
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e35
            | exact resolve b7e35 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e116 : (σ y) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b7e108
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e108
            | exact resolve b7e108 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e134 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e36 (σ y) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e161 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e116
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e116
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e116 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116
          have b7e166 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e161
               have r₂ := b7e21
               grind)
            | exact resolve b7e161 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e161
          have b7e167 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have r₁ := b7e166
               have r₂ := b7e22
               grind)
            | exact resolve b7e166 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e166
          have b7e168 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e37 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e187 : (σ x) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b7e168
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e168
            | exact resolve b7e168 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92 b7e168
          have b7e188 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e187
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e187
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e187 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e187
          have b7e195 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e188
               have r₂ := b7e21
               grind)
            | exact resolve b7e188 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e188
          have b7e196 : (σ x) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have r₁ := b7e195
               have r₂ := b7e22
               grind)
            | exact resolve b7e195 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e195
          have b7e367 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) := by
            first
            | (have i₁ := b7e134 (σ (M.op x y))
               have i₂ := b7e196
               grind)
            | exact superpose b7e196 b7e134
            | exact resolve b7e134 b7e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134 b7e196
          have b7e390 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e367
               have i₂ := b7e167
               grind)
            | exact superpose b7e167 b7e367
            | exact resolve b7e367 b7e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e167 b7e367
          have b7e1528 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e71 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e71
            | exact resolve b7e71 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e1758 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1528
          have b7e2064 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1758
               grind)
            | exact superpose b7e1758 b7e14
            | exact resolve b7e14 b7e1758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1758
          have b7e2078 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2064
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2064
            | exact resolve b7e2064 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2064
          have b7e2326 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e90 y y
               have i₂ := b7e2078
               grind)
            | exact superpose b7e2078 b7e90
            | (have j0 := b7e90 y x
               grind)
            | exact resolve b7e90 b7e2078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e2327 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2326
          have b7e2337 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2327
               have r₂ := b7e22
               grind)
            | exact resolve b7e2327 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2327
          have b7e2596 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e88 y
               have i₂ := b7e2337
               grind)
            | exact superpose b7e2337 b7e88
            | exact resolve b7e88 b7e2337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e2337
          have b7e3510 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2078
               have i₂ := b7e2596
               grind)
            | exact superpose b7e2596 b7e2078
            | exact resolve b7e2078 b7e2596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2078 b7e2596
          have b7e3513 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3510
          have b7e3515 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3513
               have r₂ := b7e22
               grind)
            | exact resolve b7e3513 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3513
          have b7e3700 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e3515
               grind)
            | exact superpose b7e3515 b7e20
            | exact resolve b7e20 b7e3515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3713 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e390
               have i₂ := b7e3515
               grind)
            | exact superpose b7e3515 b7e390
            | exact resolve b7e390 b7e3515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e390 b7e3515
          have b7e3737 : False := by grind
          exact b7e3737
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b8e308 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e309 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e308
               have r₂ := b8e24
               grind)
            | exact resolve b8e308 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e308
          have b8e310 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e309
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e309
            | exact resolve b8e309 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309
          have b8e311 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e310
               grind)
            | exact superpose b8e310 b8e20
            | exact resolve b8e20 b8e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e310
          have b8e325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e311
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e311
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e311 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e326 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e325
          have b8e327 : x = (M.op y y) := by
            first
            | (have r₁ := b8e326
               have r₂ := b8e21
               grind)
            | exact resolve b8e326 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326
          have b8e329 : False := by grind
          exact b8e329

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1483 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e59 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e62 : False := by grind
      exact b0e62
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e50 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e53 : x = y ∨ x = (k x y) := by grind
          clear b5e50
          have b5e54 : x = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e264 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e2565 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e264 x y
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e264
            | (have j0 := b5e264 x y
               grind)
            | exact resolve b5e264 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e264
          have b5e2570 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e2565
          have b5e2573 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e2570
               have r₂ := b5e24
               grind)
            | exact resolve b5e2570 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2570
          have b5e2577 : False := by grind
          exact b5e2577
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
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
          have b7e45 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e45
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
          have b7e59 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e26
               grind)
            | exact resolve b7e59 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e59
          have b7e61 : x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e62 : False := by grind
          exact b7e62
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e164 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e177 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e164
               have r₂ := b8e24
               grind)
            | exact resolve b8e164 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164
          have b8e183 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e177
               have r₂ := b8e23
               grind)
            | exact resolve b8e177 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177
          have b8e186 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e183
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e183
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e183
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e183
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e183 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183
          have b8e187 : x = (M.op x y) ∨ x = y := by grind
          clear b8e186
          have b8e188 : x = y := by
            first
            | (have r₁ := b8e187
               have r₂ := b8e22
               grind)
            | exact resolve b8e187 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187
          have b8e189 : False := by grind
          exact b8e189

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
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
      have b0e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e47 (σ X0)
           grind)
        | exact superpose b0e47 b0e17
        | exact resolve b0e17 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e53 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e53
        | exact resolve b0e53 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e53
      have b0e217 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e58 x
           grind)
        | exact superpose b0e58 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e58 x
           grind)
        | exact resolve b0e22 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e58
      have b0e228 : False := by grind
      exact b0e228
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e54 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e56 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e56
        have b1e59 : (k x y) = (M.op y y) := by grind
        clear b1e54
        have b1e60 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e60
          | exact resolve b1e60 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e57 (σ X0)
             grind)
          | exact superpose b1e57 b1e18
          | exact resolve b1e18 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e63 X0
             have i₂ := b1e57 X0
             grind)
          | exact superpose b1e57 b1e63
          | exact resolve b1e63 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e63
        have b1e76 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e78 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e76 X0
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e76
          | (have j0 := b1e76 X0
             grind)
          | exact resolve b1e76 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e136 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e23
          | exact resolve b1e23 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e896 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e78 (σ x)
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e78
          | (have j0 := b1e78 (σ x)
             grind)
          | (have r₁ := b1e78 (σ x)
             have r₂ := b1e61
             grind)
          | exact resolve b1e78 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e78
        have b1e897 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e896
        have b1e898 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e897
             have i₂ := b1e70 x
             grind)
          | exact superpose b1e70 b1e897
          | exact resolve b1e897 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e897
        have b1e900 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e898
             have r₂ := b1e136
             grind)
          | exact resolve b1e898 b1e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e898
        have b1e901 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e900
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e900
          | exact resolve b1e900 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900
        have b1e902 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e901
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e901
          | exact resolve b1e901 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e901
        have b1e903 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e902
             have i₂ := b1e70 x
             grind)
          | exact superpose b1e70 b1e902
          | exact resolve b1e902 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e902
        have b1e904 : False := by grind
        exact b1e904
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
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : (k x y) = (M.op y y) := by grind
        clear b2e51
        have b2e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e53 (σ X0)
             grind)
          | exact superpose b2e53 b2e18
          | exact resolve b2e18 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e56 X0
             have i₂ := b2e53 X0
             grind)
          | exact superpose b2e53 b2e56
          | exact resolve b2e56 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e56
        have b2e98 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e148 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e63 y
             grind)
          | exact superpose b2e63 b2e22
          | exact resolve b2e22 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e2606 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e98 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e2607 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2606
             have r₂ := b2e21
             grind)
          | exact resolve b2e2606 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2606
        have b2e2609 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2607
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2607
          | exact resolve b2e2607 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2607
        have b2e2610 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e2609
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e2609
          | exact resolve b2e2609 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e2609
        have b2e2611 : False := by grind
        exact b2e2611
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b3e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e56
        have b3e60 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e58
          | exact resolve b3e58 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e57 (σ X0)
             grind)
          | exact superpose b3e57 b3e18
          | exact resolve b3e18 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e63 X0
             have i₂ := b3e57 X0
             grind)
          | exact superpose b3e57 b3e63
          | exact resolve b3e63 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e76 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e80 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e15
          | exact resolve b3e15 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e83 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e80
        have b3e84 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e83
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e83
          | exact resolve b3e83 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e85 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e57 y
             grind)
          | exact superpose b3e57 b3e84
          | exact resolve b3e84 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e84
        have b3e86 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e85
          | exact resolve b3e85 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e261 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e70 x
             grind)
          | exact superpose b3e70 b3e23
          | exact resolve b3e23 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e70
        have b3e504 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e76 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e505 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e504
             have r₂ := b3e20
             grind)
          | exact resolve b3e504 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e504
        have b3e509 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e505
             grind)
          | exact superpose b3e505 b3e86
          | exact resolve b3e86 b3e505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86 b3e505
        have b3e513 : False := by grind
        exact b3e513
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
          have b4e70 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e70
          have b4e74 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e72
            | exact resolve b4e72 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e76 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e71 y
               grind)
            | exact superpose b4e71 b4e74
            | exact resolve b4e74 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71 b4e74
          have b4e77 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e76
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e76
            | exact resolve b4e76 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e78 : False := by grind
          exact b4e78
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b5e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e67 (σ X0)
               grind)
            | exact superpose b5e67 b5e19
            | exact resolve b5e19 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e71 X0
               have i₂ := b5e67 X0
               grind)
            | exact superpose b5e67 b5e71
            | exact resolve b5e71 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e71
          have b5e88 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e132 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e446 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e88 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e447 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e446
               have r₂ := b5e21
               grind)
            | exact resolve b5e446 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e446
          have b5e2803 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e132 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e2804 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2803
               have r₂ := b5e23
               grind)
            | exact resolve b5e2803 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2803
          have b5e2805 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2804
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2804
            | exact resolve b5e2804 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2804
          have b5e2806 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2805
               have i₂ := b5e447
               grind)
            | exact superpose b5e447 b5e2805
            | exact resolve b5e2805 b5e447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e447 b5e2805
          have b5e2809 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e2806
               grind)
            | exact superpose b5e2806 b5e23
            | exact resolve b5e23 b5e2806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2806
          have b5e2843 : False := by grind
          exact b5e2843
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
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e52
        have b6e55 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e73 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e15
          | exact resolve b6e15 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e76 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e73
        have b6e77 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e76
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e76
          | exact resolve b6e76 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e78 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e53 y
             grind)
          | exact superpose b6e53 b6e77
          | exact resolve b6e77 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e77
        have b6e137 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e78
             grind)
          | exact superpose b6e78 b6e13
          | exact resolve b6e13 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e138 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e137
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e137
          | exact resolve b6e137 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e137
        have b6e180 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e138
             grind)
          | exact superpose b6e138 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138
        have b6e181 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e180
        have b6e183 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e181
             have r₂ := b6e21
             grind)
          | exact resolve b6e181 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e181
        have b6e185 : False := by grind
        exact b6e185
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b7e66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e66
          have b7e69 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e68
            | exact resolve b7e68 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e70 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e67 y
               grind)
            | exact superpose b7e67 b7e69
            | exact resolve b7e69 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e67 (σ X0)
               grind)
            | exact superpose b7e67 b7e19
            | exact resolve b7e19 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e72 X0
               have i₂ := b7e67 X0
               grind)
            | exact superpose b7e67 b7e72
            | exact resolve b7e72 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e72
          have b7e89 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e91 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e89 X0
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e89
            | (have j0 := b7e89 X0
               grind)
            | exact resolve b7e89 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e92 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e23
            | exact resolve b7e23 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e98 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e81 x
               grind)
            | exact superpose b7e81 b7e92
            | exact resolve b7e92 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e139 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e114 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e871 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e91 (σ x)
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e91
            | (have j0 := b7e91 (σ x)
               grind)
            | (have r₁ := b7e91 (σ x)
               have r₂ := b7e70
               grind)
            | exact resolve b7e91 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e91
          have b7e872 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e871
          have b7e873 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e872
               have i₂ := b7e81 x
               grind)
            | exact superpose b7e81 b7e872
            | exact resolve b7e872 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e872
          have b7e875 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e873
               have r₂ := b7e98
               grind)
            | exact resolve b7e873 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e873
          have b7e876 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e875
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e875
            | exact resolve b7e875 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e875
          have b7e877 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e876
               have i₂ := b7e81 x
               grind)
            | exact superpose b7e81 b7e876
            | exact resolve b7e876 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e876
          have b7e879 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e877
               have i₂ := b7e139 x y
               grind)
            | exact superpose b7e139 b7e877
            | (have j1 := b7e139 x y
               grind)
            | exact resolve b7e877 b7e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e881 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e877
               grind)
            | exact superpose b7e877 b7e14
            | exact resolve b7e14 b7e877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e877
          have b7e893 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e881
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e881
            | exact resolve b7e881 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e881
          have b7e895 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e879
               have r₂ := b7e98
               grind)
            | exact resolve b7e879 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e879
          have b7e898 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e895
               have r₂ := b7e22
               grind)
            | exact resolve b7e895 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e895
          have b7e899 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e898
               have i₂ := b7e893
               grind)
            | exact superpose b7e893 b7e898
            | exact resolve b7e898 b7e893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e893 b7e898
          have b7e900 : False := by grind
          exact b7e900
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
          have b8e124 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e2614 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e124 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e2615 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e2614
               have r₂ := b8e23
               grind)
            | exact resolve b8e2614 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2614
          have b8e2616 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e2615
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e2615
            | exact resolve b8e2615 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2615
          have b8e2621 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2616
               grind)
            | exact superpose b8e2616 b8e20
            | exact resolve b8e20 b8e2616
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2616
          have b8e2745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e2621
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2621
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e2621 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2621
          have b8e2746 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e2745
          have b8e2748 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e2746
               have r₂ := b8e21
               grind)
            | exact resolve b8e2746 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2746
          have b8e2751 : False := by grind
          exact b8e2751
