import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1076 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1076 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
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
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e151 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 x y
               grind)
            | exact superpose b4e48 b4e20
            | (have j1 := b4e48 x y
               grind)
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e160 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e151
               have r₂ := b4e23
               grind)
            | exact resolve b4e151 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151
          have b4e489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e160
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e160
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e160
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e160
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e160 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e490 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e489
          have b4e491 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e490
               have r₂ := b4e21
               grind)
            | exact resolve b4e490 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e490
          have b4e494 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e491
               grind)
            | exact superpose b4e491 b4e20
            | exact resolve b4e20 b4e491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e497 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e491
               grind)
            | exact superpose b4e491 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e491
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e491
               grind)
            | exact resolve b4e17 b4e491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e491
          have b4e499 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e497
          have b4e501 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e499
               have r₂ := b4e23
               grind)
            | exact resolve b4e499 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e499
          have b4e506 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e501
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e501
            | exact resolve b4e501 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e501
          have b4e582 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e506
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e506
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e506 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e506
          have b4e604 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e582
          have b4e622 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e604
               have r₂ := b4e494
               grind)
            | exact resolve b4e604 b4e494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e494 b4e604
          have b4e623 : x = (M.op x y) := by
            first
            | (have r₁ := b4e622
               have r₂ := b4e21
               grind)
            | exact resolve b4e622 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e622
          have b4e670 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e623
               grind)
            | exact superpose b4e623 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e623
               grind)
            | exact resolve b4e17 b4e623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e672 : x = y ∨ x = (k y x) := by grind
          clear b4e670
          have b4e673 : x = (k y x) := by
            first
            | (have r₁ := b4e672
               have r₂ := b4e21
               grind)
            | exact resolve b4e672 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e672
          have b4e718 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e160
               have i₂ := b4e673
               grind)
            | exact superpose b4e673 b4e160
            | exact resolve b4e160 b4e673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160 b4e673
          have b4e722 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e718
               have i₂ := b4e623
               grind)
            | exact superpose b4e623 b4e718
            | exact resolve b4e718 b4e623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e718
          have b4e723 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e722
          have b4e754 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e723
               grind)
            | exact superpose b4e723 b4e20
            | exact resolve b4e20 b4e723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e723
          have b4e764 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e754
               have i₂ := b4e623
               grind)
            | exact superpose b4e623 b4e754
            | exact resolve b4e754 b4e623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e623 b4e754
          have b4e765 : False := by grind
          exact b4e765
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
          have b5e35 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e38 : x = y ∨ y = (k x y) := by grind
          clear b5e35
          have b5e39 : y = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e21
               grind)
            | exact resolve b5e38 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e122 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e42 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e705 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e122 y x
               have i₂ := b5e39
               grind)
            | exact superpose b5e39 b5e122
            | (have j0 := b5e122 y x
               grind)
            | exact resolve b5e122 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e122
          have b5e712 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e705
          have b5e716 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e712
               have r₂ := b5e24
               grind)
            | exact resolve b5e712 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e712
          have b5e720 : False := by grind
          exact b5e720
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
          have b7e42 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e45 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e14
            | exact resolve b7e14 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : y = (k x y) := by
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
          have b7e60 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : y = (M.op y x) ∨ x = y := by grind
          clear b7e60
          have b7e63 : x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e65 : False := by grind
          exact b7e65
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
          have b8e102 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e110 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e102
               have r₂ := b8e23
               grind)
            | exact resolve b8e102 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e351 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e110
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e110
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e110
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e110
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e110 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e352 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e351
          have b8e353 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e352
               have r₂ := b8e21
               grind)
            | exact resolve b8e352 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e352
          have b8e355 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e353
               grind)
            | exact superpose b8e353 b8e20
            | exact resolve b8e20 b8e353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e358 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e353
               grind)
            | exact superpose b8e353 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e353
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e353
               grind)
            | exact resolve b8e17 b8e353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e353
          have b8e360 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e358
          have b8e362 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e360
               have r₂ := b8e23
               grind)
            | exact resolve b8e360 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e360
          have b8e366 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e362
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e362
            | exact resolve b8e362 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e362
          have b8e431 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e366
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e366
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e366 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e366
          have b8e451 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e431
          have b8e467 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e451
               have r₂ := b8e355
               grind)
            | exact resolve b8e451 b8e355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e355 b8e451
          have b8e468 : x = (M.op x y) := by
            first
            | (have r₁ := b8e467
               have r₂ := b8e21
               grind)
            | exact resolve b8e467 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e467
          have b8e509 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e468
               grind)
            | exact resolve b8e17 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e511 : x = y ∨ x = (k y x) := by grind
          clear b8e509
          have b8e512 : x = (k y x) := by
            first
            | (have r₁ := b8e511
               have r₂ := b8e21
               grind)
            | exact resolve b8e511 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e511
          have b8e547 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e110
               have i₂ := b8e512
               grind)
            | exact superpose b8e512 b8e110
            | exact resolve b8e110 b8e512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110 b8e512
          have b8e551 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e547
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e547
            | exact resolve b8e547 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e547
          have b8e552 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e551
          have b8e580 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e552
               grind)
            | exact superpose b8e552 b8e20
            | exact resolve b8e20 b8e552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e552
          have b8e590 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e580
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e580
            | exact resolve b8e580 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e468 b8e580
          have b8e591 : False := by grind
          exact b8e591

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
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
      have b0e84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e84 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84
      have b0e152 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e87 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e87
        | exact resolve b0e87 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e153 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e87 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e87
        | exact resolve b0e87 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e155 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e152
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e152
        | exact resolve b0e152 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e152
      have b0e156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e155
           have i₂ := b0e153
           grind)
        | exact superpose b0e153 b0e155
        | exact resolve b0e155 b0e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153 b0e155
      have b0e157 : False := by grind
      exact b0e157
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
        have b1e39 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e41 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
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
        have b1e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e81 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81
        have b1e149 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e19
          | exact resolve b1e19 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e169 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e84 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e84
          | exact resolve b1e84 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e174 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e149
             have i₂ := b1e169
             grind)
          | exact superpose b1e169 b1e149
          | exact resolve b1e149 b1e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e149 b1e169
        have b1e176 : False := by grind
        exact b1e176
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
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b2e73 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e76 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e73 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e309 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e76 X0
             have i₂ := b2e54 X0 X1
             grind)
          | (have i₁ := b2e76 X0
             have i₂ := b2e54 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e54 b2e76
          | (have j1 := b2e54 X1 X0
             grind)
          | exact resolve b2e76 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e76
        have b2e335 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e309 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e309
        have b2e1322 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e335 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e335
        have b2e1323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e1322 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1322
        have b2e1395 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e1323 (σ X0)
             grind)
          | exact superpose b2e1323 b2e18
          | exact resolve b2e18 b2e1323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1402 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1395 X0
             have i₂ := b2e1323 X0
             grind)
          | exact superpose b2e1323 b2e1395
          | exact resolve b2e1395 b2e1323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1395
        have b2e1483 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e61 x x
             grind)
          | exact superpose b2e61 b2e21
          | (have j1 := b2e61 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e61 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e61 y x
             grind)
          | exact resolve b2e21 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1632 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1483
        have b2e1745 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e1632
             have i₂ := b2e1323 x
             grind)
          | exact superpose b2e1323 b2e1632
          | exact resolve b2e1632 b2e1323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1323 b2e1632
        have b2e1848 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e1745
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1745
          | exact resolve b2e1745 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1745
        have b2e1849 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1848
        have b2e1894 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1849
             have i₂ := b2e1402 x
             grind)
          | exact superpose b2e1402 b2e1849
          | exact resolve b2e1849 b2e1402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1849
        have b2e1915 : (σ x) = (σ y) := by
          first
          | (have i₁ := b2e1894
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1894
          | exact resolve b2e1894 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1894
        have b2e1959 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1915
             grind)
          | exact superpose b2e1915 b2e22
          | exact resolve b2e22 b2e1915
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1985 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1959
             have i₂ := b2e1402 x
             grind)
          | exact superpose b2e1402 b2e1959
          | exact resolve b2e1959 b2e1402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1402 b2e1959
        have b2e1993 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e1985
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1985
          | exact resolve b2e1985 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1985
        have b2e2001 : False := by grind
        exact b2e2001
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
        have b3e40 : (M.op x y) = (k y x) := by grind
        have b3e71 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e86 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e71
          | exact resolve b3e71 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e87 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e86
          | exact resolve b3e86 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e88 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e87
             have r₂ := b3e19
             grind)
          | exact resolve b3e87 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e97 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e88
        have b3e100 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e97
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e97
          | exact resolve b3e97 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e100
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e100
          | exact resolve b3e100 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e100
        have b3e102 : False := by grind
        exact b3e102
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
          have b4e45 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e46 : (M.op x y) = (k y x) := by grind
          have b4e48 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
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
          have b4e49 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e48
               have i₂ := b4e46
               grind)
            | exact superpose b4e46 b4e48
            | exact resolve b4e48 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e48
          have b4e50 : False := by grind
          exact b4e50
        · have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b5e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e305 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e84 X0
               have i₂ := b5e61 X0 X1
               grind)
            | (have i₁ := b5e84 X0
               have i₂ := b5e61 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e61 b5e84
            | (have j1 := b5e61 X1 X0
               grind)
            | exact resolve b5e84 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61 b5e84
          have b5e329 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e305 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e305
          have b5e1303 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e329 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e329
          have b5e1304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e1303 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1303
          have b5e1374 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e1304 (σ X0)
               grind)
            | exact superpose b5e1304 b5e19
            | exact resolve b5e19 b5e1304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1381 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1374 X0
               have i₂ := b5e1304 X0
               grind)
            | exact superpose b5e1304 b5e1374
            | exact resolve b5e1374 b5e1304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1374
          have b5e1463 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e68 y y
               grind)
            | exact superpose b5e68 b5e24
            | (have j1 := b5e68 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e68 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e68 x y
               grind)
            | exact resolve b5e24 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e1610 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1463
          have b5e1723 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1610
               have i₂ := b5e1304 y
               grind)
            | exact superpose b5e1304 b5e1610
            | exact resolve b5e1610 b5e1304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1304 b5e1610
          have b5e1826 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1723
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1723
            | exact resolve b5e1723 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1723
          have b5e1827 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1826
          have b5e1873 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1827
               have i₂ := b5e1381 y
               grind)
            | exact superpose b5e1381 b5e1827
            | exact resolve b5e1827 b5e1381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1827
          have b5e1894 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1873
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1873
            | exact resolve b5e1873 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1873
          have b5e1937 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1894
               grind)
            | exact superpose b5e1894 b5e20
            | exact resolve b5e20 b5e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1944 : y = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e1894
               grind)
            | exact superpose b5e1894 b5e14
            | exact resolve b5e14 b5e1894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1894
          have b5e1961 : x = y := by
            first
            | (have i₁ := b5e1944
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1944
            | exact resolve b5e1944 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1944
          have b5e1965 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1937
               have i₂ := b5e1381 x
               grind)
            | exact superpose b5e1381 b5e1937
            | exact resolve b5e1937 b5e1381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1381 b5e1937
          have b5e1970 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1965
               have i₂ := b5e1961
               grind)
            | exact superpose b5e1961 b5e1965
            | exact resolve b5e1965 b5e1961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1961 b5e1965
          have b5e1971 : False := by grind
          exact b5e1971
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e36 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e39 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
        have b6e64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e88 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e95 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e99 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e95 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e101 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e88 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e105 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e99 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e99
          | exact resolve b6e99 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e112 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e105
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e105
          | exact resolve b6e105 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e169 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e112
             grind)
          | exact superpose b6e112 b6e19
          | exact resolve b6e19 b6e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e112
        have b6e348 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e169
             have i₂ := b6e64 x y
             grind)
          | exact superpose b6e64 b6e169
          | (have j1 := b6e64 x y
             grind)
          | exact resolve b6e169 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e169
        have b6e387 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b6e348
        have b6e395 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e387
             have r₂ := b6e20
             grind)
          | exact resolve b6e387 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e387
        have b6e1636 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e69 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e69
          | exact resolve b6e69 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e1894 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1636
        have b6e1951 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1894
             grind)
          | exact superpose b6e1894 b6e13
          | exact resolve b6e13 b6e1894
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1894
        have b6e1965 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1951
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1951
          | exact resolve b6e1951 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1951
        have b6e2229 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e101 x x
             have i₂ := b6e1965
             grind)
          | exact superpose b6e1965 b6e101
          | (have j0 := b6e101 x y
             grind)
          | exact resolve b6e101 b6e1965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e2230 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2229
        have b6e2240 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2230
             have r₂ := b6e20
             grind)
          | exact resolve b6e2230 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2230
        have b6e2529 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e99 x
             have i₂ := b6e2240
             grind)
          | exact superpose b6e2240 b6e99
          | exact resolve b6e99 b6e2240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99 b6e2240
        have b6e3145 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1965
             have i₂ := b6e2529
             grind)
          | exact superpose b6e2529 b6e1965
          | exact resolve b6e1965 b6e2529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1965 b6e2529
        have b6e3148 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3145
        have b6e3150 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3148
             have r₂ := b6e20
             grind)
          | exact resolve b6e3148 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3148
        have b6e3614 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3150
             grind)
          | exact superpose b6e3150 b6e19
          | exact resolve b6e19 b6e3150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3617 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e3150
             grind)
          | exact superpose b6e3150 b6e39
          | exact resolve b6e39 b6e3150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e3626 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3150
             grind)
          | exact superpose b6e3150 b6e13
          | exact resolve b6e13 b6e3150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3643 : x = y := by
          first
          | (have i₁ := b6e3626
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3626
          | exact resolve b6e3626 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3626
        have b6e3650 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3617
             have i₂ := b6e395
             grind)
          | exact superpose b6e395 b6e3617
          | exact resolve b6e3617 b6e395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e395 b6e3617
        have b6e3651 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e3614
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3614
          | exact resolve b6e3614 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3614
        have b6e3661 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b6e3650
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3650
          | exact resolve b6e3650 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3650
        have b6e3662 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e3651
             have i₂ := b6e3150
             grind)
          | exact superpose b6e3150 b6e3651
          | exact resolve b6e3651 b6e3150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3651
        have b6e3671 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b6e3661
             have i₂ := b6e3150
             grind)
          | exact superpose b6e3150 b6e3661
          | exact resolve b6e3661 b6e3150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3150 b6e3661
        have b6e3672 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e3662
             have i₂ := b6e3643
             grind)
          | exact superpose b6e3643 b6e3662
          | exact resolve b6e3662 b6e3643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3662
        have b6e3673 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e3671
             have i₂ := b6e3643
             grind)
          | exact superpose b6e3643 b6e3671
          | exact resolve b6e3671 b6e3643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3643 b6e3671
        have b6e3674 : False := by grind
        exact b6e3674
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e46 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b7e49 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
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
          have b7e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e91 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e20
            | exact resolve b7e20 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e95 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e102 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e106 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e102 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e108 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e95 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e111 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e91
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e91 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e112 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e111
               have r₂ := b7e22
               grind)
            | exact resolve b7e111 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e113 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e112
               have r₂ := b7e21
               grind)
            | exact resolve b7e112 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e1711 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e88 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e88
            | exact resolve b7e88 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e1968 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1711
          have b7e2019 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1968
               grind)
            | exact superpose b7e1968 b7e14
            | exact resolve b7e14 b7e1968
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1968
          have b7e2033 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2019
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2019
            | exact resolve b7e2019 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2019
          have b7e2311 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e108 y y
               have i₂ := b7e2033
               grind)
            | exact superpose b7e2033 b7e108
            | (have j0 := b7e108 y x
               grind)
            | exact resolve b7e108 b7e2033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e2312 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2311
          have b7e2322 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2312
               have r₂ := b7e22
               grind)
            | exact resolve b7e2312 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2312
          have b7e2625 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e106 y
               have i₂ := b7e2322
               grind)
            | exact superpose b7e2322 b7e106
            | exact resolve b7e106 b7e2322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106 b7e2322
          have b7e3257 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2033
               have i₂ := b7e2625
               grind)
            | exact superpose b7e2625 b7e2033
            | exact resolve b7e2033 b7e2625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2033 b7e2625
          have b7e3260 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3257
          have b7e3262 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3260
               have r₂ := b7e22
               grind)
            | exact resolve b7e3260 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3260
          have b7e3658 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e3262
               grind)
            | exact superpose b7e3262 b7e14
            | exact resolve b7e14 b7e3262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3262
          have b7e3671 : x = y := by
            first
            | (have i₁ := b7e3658
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3658
            | exact resolve b7e3658 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3658
          have b7e4025 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e113
               have i₂ := b7e3671
               grind)
            | exact superpose b7e3671 b7e113
            | exact resolve b7e113 b7e3671
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113 b7e3671
          have b7e4038 : False := by grind
          exact b7e4038
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
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b8e340 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e341 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e340
               have r₂ := b8e24
               grind)
            | exact resolve b8e340 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e340
          have b8e342 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e341
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e341
            | exact resolve b8e341 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e341
          have b8e343 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e342
               grind)
            | exact superpose b8e342 b8e20
            | exact resolve b8e20 b8e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342
          have b8e350 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e343
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e343
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e343 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343
          have b8e351 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e350
          have b8e352 : x = (M.op y y) := by
            first
            | (have r₁ := b8e351
               have r₂ := b8e21
               grind)
            | exact resolve b8e351 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e351
          have b8e354 : False := by grind
          exact b8e354

/-- `Equation1487`: `x = (y ◇ x) ◇ (x ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pxx_pyy_pxy_Equation1487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e56 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e54
      have b0e57 : (M.op x x) = (k x y) := by grind
      clear b0e50
      have b0e58 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e56
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e56
        | exact resolve b0e56 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e60 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e58
           have i₂ := b0e57
           grind)
        | exact superpose b0e57 b0e58
        | exact resolve b0e58 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57 b0e58
      have b0e62 : False := by grind
      exact b0e62
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e29 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 X1 (M.op x X0) (M.op X0 (M.op x x))
             have i₂ := b1e12 X0 x x x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e29 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e29
          | exact resolve b1e29 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b1e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : (M.op x x) = (k x y) := by grind
        clear b1e55
        have b1e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e59 (σ X0)
             grind)
          | exact superpose b1e59 b1e18
          | exact resolve b1e18 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e64 X0
             have i₂ := b1e59 X0
             grind)
          | exact superpose b1e59 b1e64
          | exact resolve b1e64 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e64
        have b1e72 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e76 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e72
        have b1e77 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e76
             have r₂ := b1e21
             grind)
          | exact resolve b1e76 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e78 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e77
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e77
          | exact resolve b1e77 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e79 : (σ (M.op x x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e78
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e78
          | exact resolve b1e78 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e78
        have b1e80 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e79
             have i₂ := b1e67 y
             grind)
          | exact superpose b1e67 b1e79
          | exact resolve b1e79 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e79
        have b1e162 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e80
             grind)
          | exact superpose b1e80 b1e13
          | exact resolve b1e13 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e163 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e162
             have i₂ := b1e13 (M.op x x)
             grind)
          | exact superpose b1e13 b1e162
          | exact resolve b1e162 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e162
        have b1e178 : y = (M.op (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b1e31 y
             have i₂ := b1e163
             grind)
          | exact superpose b1e163 b1e31
          | exact resolve b1e31 b1e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e163
        have b1e188 : x = y := by
          first
          | (have i₁ := b1e178
             have i₂ := b1e29 x x x
             grind)
          | exact superpose b1e29 b1e178
          | exact resolve b1e178 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e178
        have b1e210 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e188
             grind)
          | exact superpose b1e188 b1e21
          | exact resolve b1e21 b1e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e188
        have b1e215 : False := by grind
        exact b1e215
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : (M.op x x) = (k x y) := by grind
        clear b2e51
        have b2e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e55 (σ X0)
             grind)
          | exact superpose b2e55 b2e18
          | exact resolve b2e18 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e60 X0
             have i₂ := b2e55 X0
             grind)
          | exact superpose b2e55 b2e60
          | exact resolve b2e60 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e60
        have b2e126 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
        have b2e138 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e126 X0 X1
             have i₂ := b2e63 X0
             grind)
          | exact superpose b2e63 b2e126
          | (have j0 := b2e126 X0 X1
             grind)
          | exact resolve b2e126 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126
        have b2e148 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e138 X0 X1
             have i₂ := b2e63 X0
             grind)
          | exact superpose b2e63 b2e138
          | (have j0 := b2e138 X0 X1
             grind)
          | exact resolve b2e138 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138
        have b2e993 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e148 x y
             grind)
          | exact superpose b2e148 b2e22
          | (have j1 := b2e148 x y
             grind)
          | exact resolve b2e22 b2e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e148
        have b2e1143 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e993
             have r₂ := b2e63 x
             grind)
          | exact resolve b2e993 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63 b2e993
        have b2e1196 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e1143
             have r₂ := b2e23
             grind)
          | exact resolve b2e1143 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1143
        have b2e1232 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1196
             have i₂ := b2e56
             grind)
          | exact superpose b2e56 b2e1196
          | exact resolve b2e1196 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e1196
        have b2e1250 : False := by grind
        exact b2e1250
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x x) = (M.op y x) := by grind
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
        have b3e33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 X1 (M.op x X0) (M.op X0 (M.op x x))
             have i₂ := b3e12 X0 x x x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b3e33 x X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e33
          | exact resolve b3e33 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e58
        have b3e61 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e60
          | exact resolve b3e60 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e69 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b3e76 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
        clear b3e69
        have b3e78 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e76
             have r₂ := b3e20
             grind)
          | exact resolve b3e76 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e180 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e23
          | exact resolve b3e23 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e187 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e15
          | exact resolve b3e15 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e190 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e187
        have b3e193 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e190
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e190
          | exact resolve b3e190 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e190
        have b3e199 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e180
             have i₂ := b3e78
             grind)
          | exact superpose b3e78 b3e180
          | exact resolve b3e180 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e180
        have b3e202 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e193
             have i₂ := b3e59 x
             grind)
          | exact superpose b3e59 b3e193
          | exact resolve b3e193 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e193
        have b3e209 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e202
             have i₂ := b3e78
             grind)
          | exact superpose b3e78 b3e202
          | exact resolve b3e202 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78 b3e202
        have b3e244 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e209
             grind)
          | exact superpose b3e209 b3e13
          | exact resolve b3e13 b3e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209
        have b3e245 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e244
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e244
          | exact resolve b3e244 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e244
        have b3e293 : y = (M.op (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b3e38 y
             have i₂ := b3e245
             grind)
          | exact superpose b3e245 b3e38
          | exact resolve b3e38 b3e245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e245
        have b3e305 : x = y := by
          first
          | (have i₁ := b3e293
             have i₂ := b3e33 x x x
             grind)
          | exact superpose b3e33 b3e293
          | exact resolve b3e293 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e293
        have b3e362 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e199
             have i₂ := b3e305
             grind)
          | exact superpose b3e305 b3e199
          | exact resolve b3e199 b3e305
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e199 b3e305
        have b3e363 : False := by grind
        exact b3e363
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e34 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X1 (M.op x X0) (M.op X0 (M.op x x))
               have i₂ := b4e13 X0 x x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X2 X0) X1 X0 (M.op x x)
               have i₂ := b4e13 X0 X2 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b4e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e67 (σ X0)
               grind)
            | exact superpose b4e67 b4e19
            | exact resolve b4e19 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e67 (τ X0)
               grind)
            | exact superpose b4e67 b4e26
            | exact resolve b4e26 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e72 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e71 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e71
            | exact resolve b4e71 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e69 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e69
            | exact resolve b4e69 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e76 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e72 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e72
            | exact resolve b4e72 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e72
          have b4e135 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e135 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e159 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e158 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e158
          have b4e287 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X1 (σ X0) (σ X0)
               have i₂ := b4e74 X0
               grind)
            | exact superpose b4e74 b4e34
            | exact resolve b4e34 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e320 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e14
            | exact resolve b4e14 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e448 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (M.op X2 (k X0 X1)) X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X1 X1 X1
               have i₂ := b4e159 X0 X1
               grind)
            | exact superpose b4e159 b4e35
            | (have j1 := b4e159 X0 X1
               grind)
            | exact resolve b4e35 b4e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e159
          have b4e776 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b4e287 y (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e287
            | exact resolve b4e287 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e796 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ (M.op X0 X0)) (M.op (σ X0) X1)
               have i₂ := b4e287 X0 X1
               grind)
            | exact superpose b4e287 b4e16
            | (have j0 := b4e16 (σ (M.op X0 X0)) (M.op (σ X0) X1)
               grind)
            | exact resolve b4e16 b4e287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287
          have b4e819 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e796 X0 X1
               have i₂ := b4e74 (M.op X0 X0)
               grind)
            | exact superpose b4e74 b4e796
            | (have j0 := b4e796 X0 X1
               grind)
            | exact resolve b4e796 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e796
          have b4e824 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
            first
            | (have i₁ := b4e776
               have i₂ := b4e74 x
               grind)
            | exact superpose b4e74 b4e776
            | exact resolve b4e776 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e776
          have b4e834 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e819 X0 X1
               have i₂ := b4e34 X0 X0 X0
               grind)
            | exact superpose b4e34 b4e819
            | (have j0 := b4e819 X0 X1
               grind)
            | exact resolve b4e819 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e819
          have b4e835 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e834 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e834
          have b4e838 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e835 X0 X1
               have i₂ := b4e74 (M.op X0 X0)
               grind)
            | exact superpose b4e74 b4e835
            | exact resolve b4e835 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74 b4e835
          have b4e839 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e838 X0 X1
               have i₂ := b4e34 X0 X0 X0
               grind)
            | exact superpose b4e34 b4e838
            | exact resolve b4e838 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e838
          have b4e2838 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e35 (σ (M.op x x)) x (σ (M.op y y))
               have i₂ := b4e824
               grind)
            | exact superpose b4e824 b4e35
            | exact resolve b4e35 b4e824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e824
          have b4e4559 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op (σ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e59 (M.op X0 X0) (M.op (σ X0) X1)
               have i₂ := b4e839 X0 X1
               grind)
            | exact superpose b4e839 b4e59
            | exact resolve b4e59 b4e839
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59 b4e839
          have b4e4575 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e4559 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e4559
            | exact resolve b4e4559 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4559
          have b4e20122 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) ∨ (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e448 (M.op X0 X0) (τ (M.op (σ X0) X1)) X2
               have i₂ := b4e4575 X0 X1
               grind)
            | exact superpose b4e4575 b4e448
            | (have j0 := b4e448 (M.op X0 X0) (τ (M.op (σ X0) X1)) X2
               grind)
            | exact resolve b4e448 b4e4575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e448 b4e4575
          have b4e20735 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e20122 X0 X1 X2
               have i₂ := b4e34 X0 X0 X0
               grind)
            | exact superpose b4e34 b4e20122
            | (have j0 := b4e20122 X0 X1 X0
               grind)
            | exact resolve b4e20122 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20122
          have b4e20736 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e20735 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20735
          have b4e6332206 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e20736 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20736
          have b4e6332207 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e6332206 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6332206
          have b4e6332324 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e6332207 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e6332207
            | exact resolve b4e6332207 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6332207
          have b4e6332948 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e6332324 X0 X1
               have i₂ := b4e320 X0
               grind)
            | exact superpose b4e320 b4e6332324
            | exact resolve b4e6332324 b4e320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e320 b4e6332324
          have b4e6333793 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ X0) (M.op (τ (M.op X0 X1)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 X2 (τ (M.op X0 X0)) (τ (M.op X0 X1))
               have i₂ := b4e6332948 X0 X1
               grind)
            | exact superpose b4e6332948 b4e34
            | exact resolve b4e34 b4e6332948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e6332948
          have b4e6336012 : ∀ X0 X1 : G, (τ (σ y)) = (M.op (τ (M.op X0 (σ y))) (M.op (τ (σ y)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6333793 (M.op X0 (σ y)) (σ (M.op x x)) x
               have i₂ := b4e2838 X0
               grind)
            | exact superpose b4e2838 b4e6333793
            | exact resolve b4e6333793 b4e2838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2838
          have b4e6336793 : ∀ X0 X1 : G, y = (M.op (τ (M.op X0 (σ y))) (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6336012 X0 X1
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e6336012
            | exact resolve b4e6336012 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6336012
          have b4e6336903 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e6333793 X0 (σ y) (M.op y x)
               have i₂ := b4e6336793 X0 x
               grind)
            | exact superpose b4e6336793 b4e6333793
            | exact resolve b4e6333793 b4e6336793
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6333793 b4e6336793
          have b4e6337151 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op X0 (σ y))
               have i₂ := b4e6336903 X0
               grind)
            | exact superpose b4e6336903 b4e15
            | exact resolve b4e15 b4e6336903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6336903
          have b4e6337245 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e6337151 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e6337151
            | exact resolve b4e6337151 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6337151
          have b4e6337393 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e6337245 x
               grind)
            | exact superpose b4e6337245 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e6337245 x
               grind)
            | exact resolve b4e20 b4e6337245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6337245
          have b4e6337569 : False := by grind
          exact b4e6337569
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x x) = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e34 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op x X0) (M.op X0 (M.op x x))
               have i₂ := b5e13 X0 x x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X2 X0) X1 X0 (M.op x x)
               have i₂ := b5e13 X0 X2 x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b5e34 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e34
            | exact resolve b5e34 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e26 X1 X0
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e63 (σ X0)
               grind)
            | exact superpose b5e63 b5e19
            | exact resolve b5e19 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e65 X0
               have i₂ := b5e63 X0
               grind)
            | exact superpose b5e63 b5e65
            | exact resolve b5e65 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e65
          have b5e74 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e81 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e74
          have b5e83 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e81
               have r₂ := b5e21
               grind)
            | exact resolve b5e81 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e16 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X0
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
          have b5e151 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e114 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e114
          have b5e153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e143 X0 X1
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e143
            | (have j0 := b5e143 X0 X1
               grind)
            | exact resolve b5e143 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e164 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e153 X0 X1
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e153
            | (have j0 := b5e153 X0 X1
               grind)
            | exact resolve b5e153 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e153
          have b5e275 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e34 X1 (σ X0) (σ X0)
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e34
            | exact resolve b5e34 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e533 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e151 (σ X0) (σ X1)
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e151
            | (have j0 := b5e151 (σ X0) (σ X1)
               grind)
            | exact resolve b5e151 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e577 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e151 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e151
          have b5e582 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e577 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e577 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e577 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e577 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e577 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e577
          have b5e598 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e533 X0 X1
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e533
            | (have j0 := b5e533 X0 X1
               grind)
            | exact resolve b5e533 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e533
          have b5e606 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e598 X0 X1
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e598
            | (have j0 := b5e598 X0 X1
               grind)
            | exact resolve b5e598 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e598
          have b5e771 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 (σ (M.op X0 X0)) (M.op (σ X0) X1)
               have i₂ := b5e275 X0 X1
               grind)
            | exact superpose b5e275 b5e16
            | (have j0 := b5e16 (σ (M.op X0 X0)) (M.op (σ X0) X1)
               grind)
            | exact resolve b5e16 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e275
          have b5e794 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e771 X0 X1
               have i₂ := b5e70 (M.op X0 X0)
               grind)
            | exact superpose b5e70 b5e771
            | (have j0 := b5e771 X0 X1
               grind)
            | exact resolve b5e771 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e771
          have b5e808 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e794 X0 X1
               have i₂ := b5e34 X0 X0 X0
               grind)
            | exact superpose b5e34 b5e794
            | (have j0 := b5e794 X0 X1
               grind)
            | exact resolve b5e794 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e794
          have b5e809 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e808 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e808
          have b5e812 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e809 X0 X1
               have i₂ := b5e70 (M.op X0 X0)
               grind)
            | exact superpose b5e70 b5e809
            | exact resolve b5e809 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e809
          have b5e813 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e812 X0 X1
               have i₂ := b5e34 X0 X0 X0
               grind)
            | exact superpose b5e34 b5e812
            | exact resolve b5e812 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e812
          have b5e1137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e164 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e164
          have b5e1170 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e1137 X0 X1
               have j1 := b5e606 X0 X1
               grind)
            | (have r₁ := b5e1137 X0 X1
               have r₂ := b5e606 X0 X1
               grind)
            | exact resolve b5e1137 b5e606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e606 b5e1137
          have b5e2841 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op (σ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e55 (M.op X0 X0) (M.op (σ X0) X1)
               have i₂ := b5e813 X0 X1
               grind)
            | exact superpose b5e813 b5e55
            | exact resolve b5e55 b5e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e813
          have b5e2853 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e2841 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e2841
            | exact resolve b5e2841 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2841
          have b5e7775 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1170 x y
               grind)
            | exact superpose b5e1170 b5e24
            | (have j1 := b5e1170 x y
               grind)
            | exact resolve b5e24 b5e1170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1170
          have b5e7970 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e7775
               have r₂ := b5e70 x
               grind)
            | exact resolve b5e7775 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7775
          have b5e8055 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e7970
               have i₂ := b5e83
               grind)
            | exact superpose b5e83 b5e7970
            | exact resolve b5e7970 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e7970
          have b5e8132 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e8055
               grind)
            | exact superpose b5e8055 b5e23
            | exact resolve b5e23 b5e8055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e8133 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e8055
               grind)
            | exact superpose b5e8055 b5e20
            | exact resolve b5e20 b5e8055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e8134 : x = (k (M.op x x) (τ (σ (M.op y y)))) := by
            first
            | (have i₁ := b5e2853 x (σ y)
               have i₂ := b5e8055
               grind)
            | exact superpose b5e8055 b5e2853
            | exact resolve b5e2853 b5e8055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2853 b5e8055
          have b5e8178 : x = (k (M.op x x) (M.op y y)) := by
            first
            | (have i₁ := b5e8134
               have i₂ := b5e14 (M.op y y)
               grind)
            | exact superpose b5e14 b5e8134
            | exact resolve b5e8134 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8134
          have b5e8179 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e8132
               have i₂ := b5e70 x
               grind)
            | exact superpose b5e70 b5e8132
            | exact resolve b5e8132 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e8132
          have b5e8474 : x = (M.op (M.op x x) (M.op y y)) ∨ (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op x x)) := by
            first
            | (have i₁ := b5e582 (M.op x x) (M.op y y)
               have i₂ := b5e8178
               grind)
            | exact superpose b5e8178 b5e582
            | (have j0 := b5e582 (M.op x x) (M.op y y)
               grind)
            | exact resolve b5e582 b5e8178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e582 b5e8178
          have b5e8475 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op (M.op x x) (M.op y y)) := by
            first
            | (have i₁ := b5e8474
               have i₂ := b5e39 y
               grind)
            | exact superpose b5e39 b5e8474
            | exact resolve b5e8474 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e8474
          have b5e8498 : x = (M.op (M.op x x) (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b5e8475
               have i₂ := b5e34 x x x
               grind)
            | exact superpose b5e34 b5e8475
            | exact resolve b5e8475 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e8475
          have b5e9912 : (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b5e35 y (M.op x x) y
               have i₂ := b5e8498
               grind)
            | exact superpose b5e8498 b5e35
            | exact resolve b5e35 b5e8498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e8498
          have b5e10159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b5e8133
               have i₂ := b5e9912
               grind)
            | exact superpose b5e9912 b5e8133
            | exact resolve b5e8133 b5e9912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8133 b5e9912
          have b5e10220 : x = y := by grind
          clear b5e10159
          have b5e10482 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e8179
               have i₂ := b5e10220
               grind)
            | exact superpose b5e10220 b5e8179
            | exact resolve b5e8179 b5e10220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8179 b5e10220
          have b5e10483 : False := by grind
          exact b5e10483
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x x) ≠ (M.op y x) := by grind
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
        have b6e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e56
        have b6e59 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e75 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e23
          | exact resolve b6e23 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e59
        have b6e181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e75
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e75 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e182 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by grind
        clear b6e181
        have b6e183 : (M.op x x) = (M.op y x) := by
          first
          | (have r₁ := b6e182
             have r₂ := b6e20
             grind)
          | exact resolve b6e182 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e182
        have b6e184 : False := by grind
        exact b6e184
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
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
          have b7e32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X1 (M.op x X0) (M.op X0 (M.op x x))
               have i₂ := b7e13 X0 x x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X2 X0) X1 X0 (M.op x x)
               have i₂ := b7e13 X0 X2 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e65 (σ X0)
               grind)
            | exact superpose b7e65 b7e19
            | exact resolve b7e19 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e67 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e67
            | exact resolve b7e67 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e67
          have b7e82 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e86 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e82
          have b7e87 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e23
               grind)
            | exact resolve b7e86 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e88 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e87
            | exact resolve b7e87 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e89 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e74 y
               grind)
            | exact superpose b7e74 b7e88
            | exact resolve b7e88 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e93 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e14
            | exact resolve b7e14 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (k x y) = (M.op y y) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e93
            | exact resolve b7e93 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e155 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e89
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e89 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e161 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e125 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125
          have b7e163 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have r₁ := b7e155
               have r₂ := b7e21
               grind)
            | exact resolve b7e155 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e155
          have b7e174 : (σ (M.op x y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b7e163
               have r₂ := b7e22
               grind)
            | exact resolve b7e163 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e163
          have b7e178 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e179 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have r₁ := b7e178
               have r₂ := b7e21
               grind)
            | exact resolve b7e178 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178
          have b7e181 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e179
               have r₂ := b7e22
               grind)
            | exact resolve b7e179 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e179
          have b7e206 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e32 y X0 y
               have i₂ := b7e181
               grind)
            | exact superpose b7e181 b7e32
            | exact resolve b7e32 b7e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e486 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 X1 (σ X0) (σ X0)
               have i₂ := b7e74 X0
               grind)
            | exact superpose b7e74 b7e32
            | exact resolve b7e32 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e487 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 (σ X0) X1 (σ X0)
               have i₂ := b7e74 X0
               grind)
            | exact superpose b7e74 b7e32
            | exact resolve b7e32 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e552 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e161 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e161
          have b7e557 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e552 X0 X1
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e552 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e552 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e552 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e552 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e552
          have b7e2572 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e486 y (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e486
            | exact resolve b7e486 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2587 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 (σ (M.op X0 X0)) (M.op (σ X0) X1)
               have i₂ := b7e486 X0 X1
               grind)
            | exact superpose b7e486 b7e16
            | (have j0 := b7e16 (σ (M.op X0 X0)) (M.op (σ X0) X1)
               grind)
            | exact resolve b7e16 b7e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e486
          have b7e2620 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e2587 X0 X1
               have i₂ := b7e74 (M.op X0 X0)
               grind)
            | exact superpose b7e74 b7e2587
            | (have j0 := b7e2587 X0 X1
               grind)
            | exact resolve b7e2587 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2587
          have b7e2623 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e2572
               have i₂ := b7e74 x
               grind)
            | exact superpose b7e74 b7e2572
            | exact resolve b7e2572 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2572
          have b7e2652 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e2620 X0 X1
               have i₂ := b7e32 X0 X0 X0
               grind)
            | exact superpose b7e32 b7e2620
            | (have j0 := b7e2620 X0 X1
               grind)
            | exact resolve b7e2620 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2620
          have b7e2653 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e2652 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2652
          have b7e2654 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e2623
               have i₂ := b7e174
               grind)
            | exact superpose b7e174 b7e2623
            | exact resolve b7e2623 b7e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e174 b7e2623
          have b7e2663 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e2653 X0 X1
               have i₂ := b7e74 (M.op X0 X0)
               grind)
            | exact superpose b7e74 b7e2653
            | exact resolve b7e2653 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e2653
          have b7e2669 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e2663 X0 X1
               have i₂ := b7e32 X0 X0 X0
               grind)
            | exact superpose b7e32 b7e2663
            | exact resolve b7e2663 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2663
          have b7e4998 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op (M.op x x) (M.op x x)))) := by
            first
            | (have i₁ := b7e487 (M.op x x) (σ (M.op x y))
               have i₂ := b7e2654
               grind)
            | exact superpose b7e2654 b7e487
            | exact resolve b7e487 b7e2654
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e487 b7e2654
          have b7e5045 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e4998
               have i₂ := b7e32 x x x
               grind)
            | exact superpose b7e32 b7e4998
            | exact resolve b7e4998 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4998
          have b7e6012 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op (σ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e46 (M.op X0 X0) (M.op (σ X0) X1)
               have i₂ := b7e2669 X0 X1
               grind)
            | exact superpose b7e2669 b7e46
            | exact resolve b7e46 b7e2669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46 b7e2669
          have b7e6027 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e6012 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e6012
            | exact resolve b7e6012 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6012
          have b7e7077 : y = (k (M.op y y) (τ (σ (M.op x x)))) := by
            first
            | (have i₁ := b7e6027 y (σ x)
               have i₂ := b7e5045
               grind)
            | exact superpose b7e5045 b7e6027
            | exact resolve b7e6027 b7e5045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5045 b7e6027
          have b7e7137 : y = (k (M.op y y) (M.op x x)) := by
            first
            | (have i₁ := b7e7077
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e7077
            | exact resolve b7e7077 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7077
          have b7e7172 : y = (k (M.op x y) (M.op x x)) := by
            first
            | (have i₁ := b7e7137
               have i₂ := b7e181
               grind)
            | exact superpose b7e181 b7e7137
            | exact resolve b7e7137 b7e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e181 b7e7137
          have b7e7364 : y = (M.op (M.op x y) (M.op x x)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
            first
            | (have i₁ := b7e557 (M.op x y) (M.op x x)
               have i₂ := b7e7172
               grind)
            | exact superpose b7e7172 b7e557
            | (have j0 := b7e557 (M.op x y) (M.op x x)
               grind)
            | exact resolve b7e557 b7e7172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e557 b7e7172
          have b7e7365 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x x)) := by
            first
            | (have i₁ := b7e7364
               have i₂ := b7e32 y x x
               grind)
            | exact superpose b7e32 b7e7364
            | exact resolve b7e7364 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e7364
          have b7e7391 : y = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b7e7365
               have i₂ := b7e206 x
               grind)
            | exact superpose b7e206 b7e7365
            | exact resolve b7e7365 b7e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e206 b7e7365
          have b7e12745 : (M.op x x) = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e33 x (M.op x y) x
               have i₂ := b7e7391
               grind)
            | exact superpose b7e7391 b7e33
            | exact resolve b7e33 b7e7391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e7391
          have b7e12808 : x = y := by
            first
            | (have r₁ := b7e12745
               have r₂ := b7e22
               grind)
            | exact resolve b7e12745 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12745
          have b7e13462 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e12808
               grind)
            | exact superpose b7e12808 b7e23
            | exact resolve b7e23 b7e12808
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12808
          have b7e13486 : False := by grind
          exact b7e13486
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e61 (σ X0)
               grind)
            | exact superpose b8e61 b8e19
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e63 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e63
            | exact resolve b8e63 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e63
          have b8e124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
          have b8e160 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e124 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e163 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e150 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e150
            | (have j0 := b8e150 X0 X1
               grind)
            | exact resolve b8e150 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150
          have b8e174 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e163 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e163
            | (have j0 := b8e163 X0 X1
               grind)
            | exact resolve b8e163 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e163
          have b8e590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e160 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e160
            | (have j0 := b8e160 (σ X0) (σ X1)
               grind)
            | exact resolve b8e160 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e637 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e160 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160
          have b8e642 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e637 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e637 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e637 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e637 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e637 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e637
          have b8e659 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e590 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e590
            | (have j0 := b8e590 X0 X1
               grind)
            | exact resolve b8e590 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e590
          have b8e667 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e659 X0 X1
               have i₂ := b8e70 X0
               grind)
            | exact superpose b8e70 b8e659
            | (have j0 := b8e659 X0 X1
               grind)
            | exact resolve b8e659 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e659
          have b8e1263 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e174 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e1299 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e1263 X0 X1
               have j1 := b8e667 X0 X1
               grind)
            | (have r₁ := b8e1263 X0 X1
               have r₂ := b8e667 X0 X1
               grind)
            | exact resolve b8e1263 b8e667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e667 b8e1263
          have b8e7862 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e1299 x y
               grind)
            | exact superpose b8e1299 b8e24
            | (have j1 := b8e1299 x y
               grind)
            | exact resolve b8e24 b8e1299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1299
          have b8e8066 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e7862
               have r₂ := b8e70 x
               grind)
            | exact resolve b8e7862 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70 b8e7862
          have b8e8213 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e8066
               grind)
            | exact superpose b8e8066 b8e20
            | exact resolve b8e20 b8e8066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8066
          have b8e8339 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b8e8213
               have i₂ := b8e642 x y
               grind)
            | exact superpose b8e642 b8e8213
            | (have j1 := b8e642 x y
               grind)
            | exact resolve b8e8213 b8e642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e642 b8e8213
          have b8e8340 : (M.op x x) = (M.op y x) := by grind
          clear b8e8339
          have b8e8347 : False := by grind
          exact b8e8347

/-- `Equation2700`: `x = ((y ◇ x) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation2700 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2700 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2700.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X1)) X1) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e25 : y = (M.op (M.op (M.op x y) (M.op x x)) x) := by
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
      have b0e43 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
      have b0e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear b0e43
      have b0e46 : (k x y) = (M.op y y) := by grind
      clear b0e41
      have b0e47 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e47
        | exact resolve b0e47 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e47
      have b0e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e44 (σ X0)
           grind)
        | exact superpose b0e44 b0e17
        | exact resolve b0e17 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e50 X0
           have i₂ := b0e44 X0
           grind)
        | exact superpose b0e44 b0e50
        | exact resolve b0e50 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e50
      have b0e78 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X0)) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1242 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e78 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e78
        | (have j0 := b0e78 (σ x) (σ y)
           grind)
        | exact resolve b0e78 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1246 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e78 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e78
        | (have j0 := b0e78 x y
           grind)
        | exact resolve b0e78 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1273 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op (M.op (M.op X1 X1) (M.op X0 X1)) X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e78 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e78 X0 X1
           grind)
        | exact superpose b0e78 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e78 X1 X0
           grind)
        | (have r₁ := b0e14 X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0))
           have r₂ := b0e78 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b0e14 X1 X0
           have r₂ := b0e78 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e78 X0 X0
           grind)
        | exact resolve b0e14 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e1317 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X1)) X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e1273 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1273
      have b0e1320 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e1246
           have i₂ := b0e11 x x
           grind)
        | exact superpose b0e11 b0e1246
        | exact resolve b0e1246 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1246
      have b0e1324 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1242
           have i₂ := b0e11 (σ x) (σ x)
           grind)
        | exact superpose b0e11 b0e1242
        | exact resolve b0e1242 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1242
      have b0e1332 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1324
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e1324
        | exact resolve b0e1324 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1324
      have b0e1338 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e1332
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e1332
        | exact resolve b0e1332 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1332
      have b0e8162 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1317 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1317
        | (have j0 := b0e1317 (σ y) (σ x)
           grind)
        | exact resolve b0e1317 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8167 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e1317 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1317
        | (have j0 := b0e1317 y x
           grind)
        | exact resolve b0e1317 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1317
      have b0e8279 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e8167
           have i₂ := b0e11 x x
           grind)
        | exact superpose b0e11 b0e8167
        | exact resolve b0e8167 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8167
      have b0e8284 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8162
           have i₂ := b0e11 (σ x) (σ x)
           grind)
        | exact superpose b0e11 b0e8162
        | exact resolve b0e8162 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8162
      have b0e8307 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8284
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8284
        | exact resolve b0e8284 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8284
      have b0e8320 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8307
           have i₂ := b0e55 x
           grind)
        | exact superpose b0e55 b0e8307
        | exact resolve b0e8307 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8307
      have b0e8331 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8320
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8320
        | exact resolve b0e8320 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8320
      have b0e8351 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by grind
      have b0e8368 : (M.op (σ x) (σ x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e1338
           grind)
        | exact superpose b0e1338 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | exact resolve b0e15 b0e1338
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8394 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
      clear b0e1338
      have b0e8406 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8368
           have i₂ := b0e55 x
           grind)
        | exact superpose b0e55 b0e8368
        | exact resolve b0e8368 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8368
      have b0e8425 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8406
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e8406
        | exact resolve b0e8406 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8406
      have b0e8438 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e8425
           have r₂ := b0e8394
           grind)
        | exact resolve b0e8425 b0e8394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8425
      have b0e8443 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8438
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8438
        | exact resolve b0e8438 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8438
      have b0e8446 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8443
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e8443
        | exact resolve b0e8443 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e8443
      have b0e8447 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e8446
           have r₂ := b0e8394
           grind)
        | exact resolve b0e8446 b0e8394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8394 b0e8446
      have b0e38355 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e8331
           grind)
        | exact superpose b0e8331 b0e18
        | exact resolve b0e18 b0e8331
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8331
      have b0e39736 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e38355
           have i₂ := b0e8279
           grind)
        | exact superpose b0e8279 b0e38355
        | exact resolve b0e38355 b0e8279
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8279
      have b0e39737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e38355
           have i₂ := b0e1320
           grind)
        | exact superpose b0e1320 b0e38355
        | exact resolve b0e38355 b0e1320
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1320 b0e38355
      have b0e39766 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
      clear b0e39737
      have b0e39767 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) ∨ x = y := by grind
      clear b0e39736
      have b0e42350 : (M.op x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e39766
           grind)
        | exact superpose b0e39766 b0e12
        | exact resolve b0e12 b0e39766
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39766
      have b0e42419 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e42350
           have i₂ := b0e12 (M.op x x)
           grind)
        | exact superpose b0e12 b0e42350
        | exact resolve b0e42350 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42350
      have b0e43787 : (M.op x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e39767
           grind)
        | exact superpose b0e39767 b0e12
        | exact resolve b0e12 b0e39767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39767
      have b0e43856 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e43787
           have i₂ := b0e12 (M.op x x)
           grind)
        | exact superpose b0e12 b0e43787
        | exact resolve b0e43787 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43787
      have b0e43857 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b0e43856
           have r₂ := b0e8351
           grind)
        | exact resolve b0e43856 b0e8351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8351 b0e43856
      have b0e44474 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e8447
           have i₂ := b0e43857
           grind)
        | exact superpose b0e43857 b0e8447
        | exact resolve b0e8447 b0e43857
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8447 b0e43857
      have b0e44517 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e44474
      have b0e44518 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e44517
      have b0e44556 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e44518
           grind)
        | exact superpose b0e44518 b0e18
        | exact resolve b0e18 b0e44518
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44518
      have b0e45429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e44556
           have i₂ := b0e42419
           grind)
        | exact superpose b0e42419 b0e44556
        | exact resolve b0e44556 b0e42419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42419 b0e44556
      have b0e45431 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e45429
      have b0e45432 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e45431
      have b0e45570 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e25
           have i₂ := b0e45432
           grind)
        | exact superpose b0e45432 b0e25
        | exact resolve b0e25 b0e45432
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e45432
      have b0e45628 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e45570
           have i₂ := b0e11 x x
           grind)
        | exact superpose b0e11 b0e45570
        | exact resolve b0e45570 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45570
      have b0e45629 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e45628
      have b0e45799 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e45629
           grind)
        | exact superpose b0e45629 b0e12
        | exact resolve b0e12 b0e45629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45629
      have b0e45866 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e45799
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e45799
        | exact resolve b0e45799 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45799
      have b0e45867 : x = y := by grind
      clear b0e45866
      have b0e46424 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e45867
           grind)
        | exact superpose b0e45867 b0e18
        | exact resolve b0e18 b0e45867
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45867
      have b0e46474 : False := by grind
      exact b0e46474
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e51 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e53 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b1e53
        have b1e57 : (k x y) = (M.op y y) := by grind
        clear b1e51
        have b1e58 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e56
          | exact resolve b1e56 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e58
          | exact resolve b1e58 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e55 (σ X0)
             grind)
          | exact superpose b1e55 b1e18
          | exact resolve b1e18 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e61 X0
             have i₂ := b1e55 X0
             grind)
          | exact superpose b1e55 b1e61
          | exact resolve b1e61 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e61
        have b1e74 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e76 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e74 X0
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e74
          | (have j0 := b1e74 X0
             grind)
          | exact resolve b1e74 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e131 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e21
          | exact resolve b1e21 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e136 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e131
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e131
          | exact resolve b1e131 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e772 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e76 (σ x)
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e76
          | (have j0 := b1e76 (σ x)
             grind)
          | (have r₁ := b1e76 (σ x)
             have r₂ := b1e59
             grind)
          | exact resolve b1e76 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e76
        have b1e774 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e772
        have b1e775 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e774
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e774
          | exact resolve b1e774 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774
        have b1e776 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e775
             have r₂ := b1e136
             grind)
          | exact resolve b1e775 b1e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e775
        have b1e777 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e776
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e776
          | exact resolve b1e776 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e776
        have b1e778 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e777
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e777
          | exact resolve b1e777 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e777
        have b1e779 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e778
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e778
          | exact resolve b1e778 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e778
        have b1e780 : False := by grind
        exact b1e780
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (k x y) = (M.op y y) := by grind
        clear b2e49
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e51 (σ X0)
             grind)
          | exact superpose b2e51 b2e18
          | exact resolve b2e18 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e54
          | exact resolve b2e54 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e54
        have b2e94 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b2e142 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
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
        have b2e1407 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e94 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e1408 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1407
             have r₂ := b2e21
             grind)
          | exact resolve b2e1407 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1407
        have b2e1409 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1408
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1408
          | exact resolve b2e1408 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1408
        have b2e1410 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1409
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e1409
          | exact resolve b2e1409 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e1409
        have b2e1411 : False := by grind
        exact b2e1411
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : (M.op y x) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e53
        have b3e58 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e56
          | exact resolve b3e56 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e74 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e15
          | exact resolve b3e15 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e81 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e76
        have b3e84 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e81
          | exact resolve b3e81 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e85 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e55 y
             grind)
          | exact superpose b3e55 b3e84
          | exact resolve b3e84 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e84
        have b3e86 : (σ (k x y)) = (σ (M.op y x)) := by
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
        have b3e140 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e86
             grind)
          | exact superpose b3e86 b3e13
          | exact resolve b3e13 b3e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e141 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e140
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e140
          | exact resolve b3e140 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e140
        have b3e374 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e74 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e375 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e374
             have r₂ := b3e20
             grind)
          | exact resolve b3e374 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e374
        have b3e378 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e141
             have i₂ := b3e375
             grind)
          | exact superpose b3e375 b3e141
          | exact resolve b3e141 b3e375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141 b3e375
        have b3e383 : False := by grind
        exact b3e383
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X1)) X1) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
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
          have b4e33 : y = (M.op (M.op (M.op y x) (M.op y x)) y) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b4e52 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (σ y)) := by
            first
            | (have i₁ := b4e13 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b4e67
          have b4e73 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e71
            | exact resolve b4e71 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e75 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e70 y
               grind)
            | exact superpose b4e70 b4e73
            | exact resolve b4e73 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e76 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e75
            | exact resolve b4e75 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e70 (σ X0)
               grind)
            | exact superpose b4e70 b4e19
            | exact resolve b4e19 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e70 (τ X0)
               grind)
            | exact superpose b4e70 b4e26
            | exact resolve b4e26 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e81 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e81
            | exact resolve b4e81 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e78 X0
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e78
            | exact resolve b4e78 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e84 X0
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e84
            | exact resolve b4e84 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e84
          have b4e99 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e23
            | exact resolve b4e23 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102 : (σ x) = (M.op (M.op (σ (M.op y x)) (M.op (σ x) (σ y))) (σ y)) := by
            first
            | (have i₁ := b4e13 (σ x) (σ y)
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e13
            | exact resolve b4e13 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104 : (σ (M.op y x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e99
               have i₂ := b4e87 x
               grind)
            | exact superpose b4e87 b4e99
            | exact resolve b4e99 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e114 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X0)) X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e13 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X1
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e134 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e140 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e123 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123
          have b4e144 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e113 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113
          have b4e147 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e134 X0 X1
               have i₂ := b4e87 X1
               grind)
            | exact superpose b4e87 b4e134
            | (have j0 := b4e134 X0 X1
               grind)
            | exact resolve b4e134 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e150 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e142 X0 X1
               have j1 := b4e140 X0 X1
               grind)
            | (have r₁ := b4e142 X0 X1
               have r₂ := b4e140 X0 X1
               grind)
            | (have r₁ := b4e142 X1 X0
               have r₂ := b4e140 X0 X1
               grind)
            | (have r₁ := b4e142 X1 X1
               have r₂ := b4e140 X1 X1
               grind)
            | exact resolve b4e142 b4e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e156 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e147 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e147
            | (have j0 := b4e147 X0 X1
               grind)
            | exact resolve b4e147 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147
          have b4e176 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 (σ X0)
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e17
            | (have j0 := b4e17 X1 (σ X0)
               grind)
            | exact resolve b4e17 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e201 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e90 X0
               grind)
            | exact superpose b4e90 b4e14
            | exact resolve b4e14 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e207 : (σ y) = (M.op (M.op (σ (M.op y x)) (σ (M.op y x))) (σ y)) := by
            first
            | (have i₁ := b4e52
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e52
            | exact resolve b4e52 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e218 : (σ y) = (M.op (σ (M.op (M.op y x) (M.op y x))) (σ y)) := by
            first
            | (have i₁ := b4e207
               have i₂ := b4e87 (M.op y x)
               grind)
            | exact superpose b4e87 b4e207
            | exact resolve b4e207 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e207
          have b4e293 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (τ X0) X1
               have i₂ := b4e201 X0
               grind)
            | exact superpose b4e201 b4e16
            | (have j0 := b4e16 (τ X0) X1
               grind)
            | exact resolve b4e16 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e514 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y x) ∨ (M.op y x) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e140 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e140
            | (have j0 := b4e140 X0 y
               grind)
            | exact resolve b4e140 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e140
          have b4e549 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e144 (τ X1) X0
               grind)
            | exact superpose b4e144 b4e25
            | (have j1 := b4e144 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e587 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e144 (τ X1) X0
               grind)
            | exact superpose b4e144 b4e25
            | (have j1 := b4e144 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e738 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X0 X1
               have i₂ := b4e150 X1 (τ X0)
               grind)
            | exact superpose b4e150 b4e25
            | (have j1 := b4e150 X1 (τ X0)
               grind)
            | exact resolve b4e25 b4e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e150
          have b4e765 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e738 X0 X1
               have i₂ := b4e90 X0
               grind)
            | exact superpose b4e90 b4e738
            | (have j0 := b4e738 X0 X1
               grind)
            | exact resolve b4e738 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90 b4e738
          have b4e791 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e765 X0 X1
               have i₂ := b4e201 X0
               grind)
            | exact superpose b4e201 b4e765
            | (have j0 := b4e765 X0 X1
               grind)
            | exact resolve b4e765 b4e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201 b4e765
          have b4e973 : ∀ X0 : G, (M.op (M.op (M.op y X0) (M.op y x)) y) = X0 ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e114 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e114
            | (have j0 := b4e114 y X0
               grind)
            | exact resolve b4e114 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e997 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X1)) X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e114 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e114 X0 X1
               grind)
            | exact superpose b4e114 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e114 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e114 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e114 X0 X0
               grind)
            | exact resolve b4e17 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114
          have b4e1032 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X1)) X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e997 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e997
          have b4e3649 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e156 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156
          have b4e10331 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e973 x
               grind)
            | exact superpose b4e973 b4e33
            | (have j1 := b4e973 x
               grind)
            | exact resolve b4e33 b4e973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e973
          have b4e14514 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e549 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e549
            | (have j0 := b4e549 X1 (σ X0)
               grind)
            | exact resolve b4e549 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e549
          have b4e14764 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e14514 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e14514
            | (have j0 := b4e14514 X0 X1
               grind)
            | exact resolve b4e14514 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14514
          have b4e15352 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e587 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e587
            | exact resolve b4e587 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e587
          have b4e15689 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e15352 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e15352
            | (have j0 := b4e15352 X0 X1
               grind)
            | exact resolve b4e15352 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15352
          have b4e17621 : ∀ X0 : G, (M.op X0 (τ (σ y))) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e791 (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e791
            | (have j0 := b4e791 (σ y) X0
               grind)
            | exact resolve b4e791 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e17813 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e293 X0 X1
               have i₂ := b4e791 X0 X1
               grind)
            | exact superpose b4e791 b4e293
            | (have j0 := b4e293 X0 X1
               have j1 := b4e791 X0 X1
               grind)
            | (have r₁ := b4e293 X0 X1
               have r₂ := b4e791 X0 X1
               grind)
            | exact resolve b4e293 b4e791
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293 b4e791
          have b4e18097 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e17813 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17813
          have b4e18275 : ∀ X0 : G, (M.op X0 (τ (σ y))) = (τ (σ (M.op y x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e17621 X0
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e17621
            | (have j0 := b4e17621 X0
               grind)
            | exact resolve b4e17621 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17621
          have b4e18383 : ∀ X0 : G, (M.op y x) = (M.op X0 (τ (σ y))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e18275 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e18275
            | (have j0 := b4e18275 X0
               grind)
            | exact resolve b4e18275 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18275
          have b4e18451 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e18383 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e18383
            | (have j0 := b4e18383 X0
               grind)
            | exact resolve b4e18383 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18383
          have b4e18494 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k y X0)) ∨ (M.op y x) = (M.op X0 y) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e18451 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e18451
            | (have j0 := b4e18451 X0
               grind)
            | exact resolve b4e18451 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18451
          have b4e18515 : ∀ X0 : G, (σ (M.op y x)) = (σ (k y X0)) ∨ (M.op y x) = (M.op X0 y) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e18494 X0
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e18494
            | (have j0 := b4e18494 X0
               grind)
            | exact resolve b4e18494 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18494
          have b4e18527 : ∀ X0 : G, (σ (M.op y x)) = (σ (k y X0)) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e18515 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e18515
            | (have j0 := b4e18515 X0
               grind)
            | exact resolve b4e18515 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18515
          have b4e23721 : ∀ X0 : G, (k y X0) = (τ (σ (M.op y x))) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e14 (k y X0)
               have i₂ := b4e18527 X0
               grind)
            | exact superpose b4e18527 b4e14
            | (have j1 := b4e18527 X0
               grind)
            | exact resolve b4e14 b4e18527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18527
          have b4e23782 : ∀ X0 : G, (M.op y x) = (k y X0) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e23721 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e23721
            | (have j0 := b4e23721 X0
               grind)
            | exact resolve b4e23721 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23721
          have b4e24484 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y x) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e144 y X0
               have i₂ := b4e23782 X0
               grind)
            | exact superpose b4e23782 b4e144
            | (have j0 := b4e144 y X0
               have j1 := b4e23782 X0
               grind)
            | exact resolve b4e144 b4e23782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144 b4e23782
          have b4e24533 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y x) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e24484 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24484
          have b4e24555 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e24533 X0
               have j1 := b4e514 X0
               grind)
            | (have r₁ := b4e24533 y
               have r₂ := b4e514 y
               grind)
            | (have r₁ := b4e24533 X0
               have r₂ := b4e514 X0
               grind)
            | exact resolve b4e24533 b4e514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e514 b4e24533
          have b4e24931 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e24555 X0
               have i₂ := b4e15689 y X0
               grind)
            | exact superpose b4e15689 b4e24555
            | (have j0 := b4e24555 X0
               have j1 := b4e15689 y X0
               grind)
            | exact resolve b4e24555 b4e15689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15689
          have b4e25136 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e24931 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24931
          have b4e53669 : (σ x) = (M.op (M.op (σ (M.op y x)) (M.op (σ y) (σ y))) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e1032 (σ x) (σ y)
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e1032
            | (have j0 := b4e1032 (σ x) (σ y)
               grind)
            | exact resolve b4e1032 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1032
          have b4e54642 : (σ x) = (M.op (M.op (σ (M.op y x)) (M.op (σ y) (σ x))) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e53669
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e53669
            | exact resolve b4e53669 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53669
          have b4e54786 : (σ x) = (M.op (M.op (σ (M.op y x)) (σ (M.op y x))) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e54642
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e54642
            | exact resolve b4e54642 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54642
          have b4e54894 : (σ x) = (M.op (σ (M.op (M.op y x) (M.op y x))) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e54786
               have i₂ := b4e87 (M.op y x)
               grind)
            | exact superpose b4e87 b4e54786
            | exact resolve b4e54786 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54786
          have b4e54967 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e54894
               have i₂ := b4e218
               grind)
            | exact superpose b4e218 b4e54894
            | exact resolve b4e54894 b4e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54894
          have b4e55023 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e54967
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e54967
            | exact resolve b4e54967 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54967
          have b4e55069 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b4e55023
               have r₂ := b4e23
               grind)
            | exact resolve b4e55023 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55023
          have b4e55109 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e55069
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e55069
            | exact resolve b4e55069 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55069
          have b4e55140 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e55109
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e55109
            | exact resolve b4e55109 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55109
          have b4e55168 : (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e55140
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e55140
            | exact resolve b4e55140 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55140
          have b4e55191 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e55168
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e55168
            | exact resolve b4e55168 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55168
          have b4e55316 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e55191
               grind)
            | exact superpose b4e55191 b4e20
            | exact resolve b4e20 b4e55191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e55324 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e176 x (σ y)
               have i₂ := b4e55191
               grind)
            | exact superpose b4e55191 b4e176
            | (have j0 := b4e176 x (σ y)
               grind)
            | exact resolve b4e176 b4e55191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176 b4e55191
          have b4e55402 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e55324
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e55324
            | exact resolve b4e55324 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55324
          have b4e55430 : (σ (M.op y x)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e55402
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e55402
            | exact resolve b4e55402 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55402
          have b4e55431 : (σ (M.op y x)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b4e55430
          have b4e55449 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e55431
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e55431
            | exact resolve b4e55431 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55431
          have b4e55458 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e55449
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e55449
            | exact resolve b4e55449 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55449
          have b4e55464 : (σ (M.op y x)) = (σ (k y x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e55458
               have i₂ := b4e76
               grind)
            | exact superpose b4e76 b4e55458
            | exact resolve b4e55458 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e55458
          have b4e55465 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ (M.op y x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b4e55464
          have b4e56625 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e55465
               have i₂ := b4e14764 y x
               grind)
            | exact superpose b4e14764 b4e55465
            | (have j1 := b4e14764 y x
               grind)
            | (have r₁ := b4e55465
               have r₂ := b4e14764 y x
               grind)
            | exact resolve b4e55465 b4e14764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14764 b4e55465
          have b4e56626 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e56625
          have b4e56627 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b4e56626
               have r₂ := b4e104
               grind)
            | exact resolve b4e56626 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56626
          have b4e57063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e55316
               have i₂ := b4e56627
               grind)
            | exact superpose b4e56627 b4e55316
            | exact resolve b4e55316 b4e56627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55316 b4e56627
          have b4e57074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e57063
          have b4e57075 : (σ (M.op x y)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e57074
          have b4e57236 : (M.op y x) = (τ (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op y x)
               have i₂ := b4e57075
               grind)
            | exact superpose b4e57075 b4e14
            | exact resolve b4e14 b4e57075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57075
          have b4e57308 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e57236
               have i₂ := b4e14 (M.op x y)
               grind)
            | exact superpose b4e14 b4e57236
            | exact resolve b4e57236 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57236
          have b4e58123 : y = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e57308
               grind)
            | exact superpose b4e57308 b4e33
            | exact resolve b4e33 b4e57308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e58192 : x = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e13 x y
               have i₂ := b4e57308
               grind)
            | exact superpose b4e57308 b4e13
            | exact resolve b4e13 b4e57308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57308
          have b4e61932 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e58123
               have i₂ := b4e58192
               grind)
            | exact superpose b4e58192 b4e58123
            | exact resolve b4e58123 b4e58192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58123 b4e58192
          have b4e61982 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b4e61932
          have b4e111101 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X0 (σ X1)
               have i₂ := b4e18097 (σ X0) X1
               grind)
            | exact superpose b4e18097 b4e40
            | (have j1 := b4e18097 (σ X0) X1
               grind)
            | exact resolve b4e40 b4e18097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18097
          have b4e111514 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e111101 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e111101
            | (have j0 := b4e111101 X0 X1
               grind)
            | exact resolve b4e111101 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111101
          have b4e112015 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e111514 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e111514
            | (have j0 := b4e111514 X0 X1
               grind)
            | exact resolve b4e111514 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111514
          have b4e112280 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e112015 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e112015
            | (have j0 := b4e112015 X0 X1
               grind)
            | exact resolve b4e112015 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112015
          have b4e112478 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e112280 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e112280
            | (have j0 := b4e112280 X0 X1
               grind)
            | exact resolve b4e112280 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112280
          have b4e112589 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e112478 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e112478
            | (have j0 := b4e112478 X0 X1
               grind)
            | exact resolve b4e112478 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112478
          have b4e117178 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X0 X1
               have i₂ := b4e112589 (σ X0) X1
               grind)
            | exact superpose b4e112589 b4e40
            | (have j1 := b4e112589 (σ X0) X1
               grind)
            | exact resolve b4e40 b4e112589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e117313 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112589 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112589
          have b4e117581 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e117178 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e117178
            | (have j0 := b4e117178 X0 X1
               grind)
            | exact resolve b4e117178 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117178
          have b4e118298 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e117581 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e117581
            | (have j0 := b4e117581 X0 X1
               grind)
            | exact resolve b4e117581 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117581
          have b4e121858 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e117313 y X0
               have i₂ := b4e25136 X0
               grind)
            | (have i₁ := b4e117313 X0 X0
               have i₂ := b4e25136 X0
               grind)
            | exact superpose b4e25136 b4e117313
            | (have j0 := b4e117313 y X0
               have j1 := b4e25136 X0
               grind)
            | (have r₁ := b4e117313 y y
               have r₂ := b4e25136 y
               grind)
            | (have r₁ := b4e117313 y X0
               have r₂ := b4e25136 X0
               grind)
            | (have r₁ := b4e117313 x y
               have r₂ := b4e25136 y
               grind)
            | exact resolve b4e117313 b4e25136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25136 b4e117313
          have b4e121990 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e121858 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121858
          have b4e122150 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have j0 := b4e121990 X0
               have j1 := b4e68 X0
               grind)
            | (have r₁ := b4e121990 X0
               have r₂ := b4e68 X0
               grind)
            | exact resolve b4e121990 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121990
          have b4e122235 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op y x) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e122150 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e122150
            | (have j0 := b4e122150 X0
               grind)
            | exact resolve b4e122150 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122150
          have b4e335245 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (σ X1) X0
               have i₂ := b4e118298 X1 (σ X0)
               grind)
            | exact superpose b4e118298 b4e30
            | (have j1 := b4e118298 X1 (σ X0)
               grind)
            | exact resolve b4e30 b4e118298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e118298
          have b4e335256 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e335245 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e335245
            | (have j0 := b4e335245 X0 X1
               grind)
            | exact resolve b4e335245 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335245
          have b4e335300 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e335256 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e335256
            | (have j0 := b4e335256 X0 X1
               grind)
            | exact resolve b4e335256 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335256
          have b4e335330 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e335300 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e335300
            | (have j0 := b4e335300 X0 X1
               grind)
            | exact resolve b4e335300 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335300
          have b4e335351 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e335330 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e335330
            | (have j0 := b4e335330 X0 X1
               grind)
            | exact resolve b4e335330 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335330
          have b4e335363 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e335351 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e335351
            | (have j0 := b4e335351 X0 X1
               grind)
            | exact resolve b4e335351 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335351
          have b4e352014 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e335363 x y
               grind)
            | exact superpose b4e335363 b4e20
            | (have j1 := b4e335363 x y
               grind)
            | exact resolve b4e20 b4e335363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335363
          have b4e352166 : (M.op y x) = (k y x) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e352014
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e352014
            | exact resolve b4e352014 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e352014
          have b4e352202 : (M.op y x) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e122235 x
               grind)
            | (have r₁ := b4e352166
               have r₂ := b4e122235 x
               grind)
            | exact resolve b4e352166 b4e122235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122235 b4e352166
          have b4e352553 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e24555 x
               have i₂ := b4e352202
               grind)
            | exact superpose b4e352202 b4e24555
            | (have j0 := b4e24555 x
               grind)
            | exact resolve b4e24555 b4e352202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e24555 b4e352202
          have b4e352599 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e352553
          have b4e352628 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have j1 := b4e68 x
               grind)
            | (have r₁ := b4e352599
               have r₂ := b4e68 x
               grind)
            | exact resolve b4e352599 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68 b4e352599
          have b4e355684 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e10331
               have i₂ := b4e352628
               grind)
            | exact superpose b4e352628 b4e10331
            | exact resolve b4e10331 b4e352628
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10331 b4e352628
          have b4e355767 : (M.op x y) = (M.op x x) ∨ x = y := by grind
          clear b4e355684
          have b4e358536 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e355767
               grind)
            | exact superpose b4e355767 b4e17
            | (have j0 := b4e17 x x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e355767
               grind)
            | exact resolve b4e17 b4e355767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e355767
          have b4e358571 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) ∨ x = y := by grind
          clear b4e358536
          have b4e358590 : (M.op x x) = (M.op y x) ∨ (M.op y y) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e358571
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e358571
            | exact resolve b4e358571 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e358571
          have b4e358594 : (M.op y y) = (k y x) ∨ x = y := by
            first
            | (have r₁ := b4e358590
               have r₂ := b4e21
               grind)
            | exact resolve b4e358590 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e358590
          have b4e358595 : (M.op y x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e358594
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e358594
            | exact resolve b4e358594 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e358594
          have b4e359228 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y := by
            first
            | (have i₁ := b4e3649 x y
               have i₂ := b4e358595
               grind)
            | exact superpose b4e358595 b4e3649
            | (have j0 := b4e3649 x y
               grind)
            | exact resolve b4e3649 b4e358595
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3649 b4e358595
          have b4e359275 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y := by
            first
            | (have i₁ := b4e359228
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e359228
            | exact resolve b4e359228 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e359228
          have b4e359276 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b4e359275
          have b4e375240 : (σ x) = (M.op (M.op (σ (M.op y x)) (σ (M.op y x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e102
               have i₂ := b4e359276
               grind)
            | exact superpose b4e359276 b4e102
            | exact resolve b4e102 b4e359276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102 b4e359276
          have b4e375262 : (σ x) = (M.op (σ (M.op (M.op y x) (M.op y x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e375240
               have i₂ := b4e87 (M.op y x)
               grind)
            | exact superpose b4e87 b4e375240
            | exact resolve b4e375240 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87 b4e375240
          have b4e375270 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b4e375262
               have i₂ := b4e218
               grind)
            | exact superpose b4e218 b4e375262
            | exact resolve b4e375262 b4e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e218 b4e375262
          have b4e376344 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e375270
               grind)
            | exact superpose b4e375270 b4e20
            | exact resolve b4e20 b4e375270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e375270
          have b4e376689 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b4e376344
               have i₂ := b4e61982
               grind)
            | exact superpose b4e61982 b4e376344
            | exact resolve b4e376344 b4e61982
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61982 b4e376344
          have b4e376690 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b4e376689
          have b4e376691 : (σ x) = (σ y) ∨ x = y := by grind
          clear b4e376690
          have b4e378112 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e376691
               grind)
            | exact superpose b4e376691 b4e23
            | exact resolve b4e23 b4e376691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e376691
          have b4e378277 : x = y := by grind
          clear b4e378112
          have b4e379851 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e104
               have i₂ := b4e378277
               grind)
            | exact superpose b4e378277 b4e104
            | exact resolve b4e104 b4e378277
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104 b4e378277
          have b4e380047 : False := by grind
          exact b4e380047
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e66 (σ X0)
               grind)
            | exact superpose b5e66 b5e19
            | exact resolve b5e19 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e70 X0
               have i₂ := b5e66 X0
               grind)
            | exact superpose b5e66 b5e70
            | exact resolve b5e70 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e70
          have b5e87 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e131 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e312 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e87 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e313 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e312
               have r₂ := b5e21
               grind)
            | exact resolve b5e312 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e312
          have b5e1544 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e131 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e1545 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1544
               have r₂ := b5e23
               grind)
            | exact resolve b5e1544 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1544
          have b5e1546 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1545
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1545
            | exact resolve b5e1545 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1545
          have b5e1547 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1546
               have i₂ := b5e313
               grind)
            | exact superpose b5e313 b5e1546
            | exact resolve b5e1546 b5e313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313 b5e1546
          have b5e1551 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1547
               grind)
            | exact superpose b5e1547 b5e23
            | exact resolve b5e23 b5e1547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1547
          have b5e1573 : False := by grind
          exact b5e1573
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e52
          | exact resolve b6e52 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e69 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e15
          | exact resolve b6e15 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e74 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e69
        have b6e77 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e74
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e74
          | exact resolve b6e74 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e78 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e51 y
             grind)
          | exact superpose b6e51 b6e77
          | exact resolve b6e77 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e77
        have b6e133 : (k x y) = (τ (σ (M.op y y))) := by
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
        have b6e134 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e133
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e133
          | exact resolve b6e133 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e133
        have b6e150 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e134
             grind)
          | exact superpose b6e134 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e151 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by grind
        clear b6e150
        have b6e153 : (M.op x x) = (M.op y x) := by
          first
          | (have r₁ := b6e151
             have r₂ := b6e21
             grind)
          | exact resolve b6e151 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e151
        have b6e155 : False := by grind
        exact b6e155
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e64 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b7e64
          have b7e68 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e67
            | exact resolve b7e67 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e69 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e66 y
               grind)
            | exact superpose b7e66 b7e68
            | exact resolve b7e68 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e66 (σ X0)
               grind)
            | exact superpose b7e66 b7e19
            | exact resolve b7e19 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e71 X0
               have i₂ := b7e66 X0
               grind)
            | exact superpose b7e66 b7e71
            | exact resolve b7e71 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e71
          have b7e88 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e90 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e88 X0
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e88
            | (have j0 := b7e88 X0
               grind)
            | exact resolve b7e88 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e91 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e23
            | exact resolve b7e23 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e91
            | exact resolve b7e91 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e136 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e105 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e745 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e90 (σ x)
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e90
            | (have j0 := b7e90 (σ x)
               grind)
            | (have r₁ := b7e90 (σ x)
               have r₂ := b7e69
               grind)
            | exact resolve b7e90 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e90
          have b7e747 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e745
          have b7e748 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e747
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e747
            | exact resolve b7e747 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e747
          have b7e749 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e748
               have r₂ := b7e96
               grind)
            | exact resolve b7e748 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e748
          have b7e750 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e749
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e749
            | exact resolve b7e749 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e749
          have b7e751 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e750
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e750
            | exact resolve b7e750 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e750
          have b7e753 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e751
               have i₂ := b7e136 x y
               grind)
            | exact superpose b7e136 b7e751
            | (have j1 := b7e136 x y
               grind)
            | exact resolve b7e751 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e755 : (k x y) = (τ (σ (M.op x x))) := by
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
          have b7e771 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e755
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e755
            | exact resolve b7e755 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e755
          have b7e773 : (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e753
               have r₂ := b7e96
               grind)
            | exact resolve b7e753 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96 b7e753
          have b7e776 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e773
               have r₂ := b7e22
               grind)
            | exact resolve b7e773 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e773
          have b7e777 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e776
               have i₂ := b7e771
               grind)
            | exact superpose b7e771 b7e776
            | exact resolve b7e776 b7e771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e771 b7e776
          have b7e778 : False := by grind
          exact b7e778
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e30
            | exact resolve b8e30 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e62 (σ X0)
               grind)
            | exact superpose b8e62 b8e19
            | exact resolve b8e19 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e62 (τ X0)
               grind)
            | exact superpose b8e62 b8e26
            | exact resolve b8e26 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e67 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e67
            | exact resolve b8e67 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e64 X0
               have i₂ := b8e62 X0
               grind)
            | exact superpose b8e62 b8e64
            | exact resolve b8e64 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e76 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
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
          have b8e90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e16
            | (have j0 := b8e16 (σ X0) X1
               grind)
            | exact resolve b8e16 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e131 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e113 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e138 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e125 X0 X1
               have i₂ := b8e73 X1
               grind)
            | exact superpose b8e73 b8e125
            | (have j0 := b8e125 X0 X1
               grind)
            | exact resolve b8e125 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125
          have b8e140 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               have j1 := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X0 X1
               have r₂ := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X1 X0
               have r₂ := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X1 X1
               have r₂ := b8e131 X1 X1
               grind)
            | exact resolve b8e133 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131 b8e133
          have b8e143 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e138 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e138
            | (have j0 := b8e138 X0 X1
               grind)
            | exact resolve b8e138 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e155 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e14
            | exact resolve b8e14 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e252 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (τ X0) X1
               have i₂ := b8e155 X0
               grind)
            | exact superpose b8e155 b8e16
            | (have j0 := b8e16 (τ X0) X1
               grind)
            | exact resolve b8e16 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e454 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e140 X1 (τ X0)
               grind)
            | exact superpose b8e140 b8e25
            | (have j1 := b8e140 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e466 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e140 (τ X0) X1
               grind)
            | exact superpose b8e140 b8e26
            | (have j1 := b8e140 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e481 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e454 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e454
            | (have j0 := b8e454 X0 X1
               grind)
            | exact resolve b8e454 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e454
          have b8e500 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e481 X0 X1
               have i₂ := b8e155 X0
               grind)
            | exact superpose b8e155 b8e481
            | (have j0 := b8e481 X0 X1
               grind)
            | exact resolve b8e481 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155 b8e481
          have b8e2055 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e143 X1 X0
               grind)
            | exact superpose b8e143 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e143 X1 X0
               grind)
            | exact resolve b8e16 b8e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2078 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2079 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2080 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e2141 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e2055 X0 X1
               have j1 := b8e90 X0 (σ X1)
               grind)
            | (have r₁ := b8e2055 X0 X0
               have r₂ := b8e90 X0 (σ X0)
               grind)
            | (have r₁ := b8e2055 X0 X1
               have r₂ := b8e90 X0 (σ X1)
               grind)
            | exact resolve b8e2055 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e2055
          have b8e2210 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2141 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e2141
            | (have j0 := b8e2141 X0 X1
               grind)
            | exact resolve b8e2141 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2141
          have b8e2259 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2210 X0 X1
               have i₂ := b8e73 X1
               grind)
            | exact superpose b8e73 b8e2210
            | (have j0 := b8e2210 X0 X1
               grind)
            | exact resolve b8e2210 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2210
          have b8e2290 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2259 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e2259
            | (have j0 := b8e2259 X0 X1
               grind)
            | exact resolve b8e2259 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2259
          have b8e7418 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e466 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e466
            | exact resolve b8e466 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e466
          have b8e7650 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e7418 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e7418
            | (have j0 := b8e7418 X0 X1
               grind)
            | exact resolve b8e7418 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7418
          have b8e8014 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e252 X0 X1
               have i₂ := b8e500 X0 X1
               grind)
            | exact superpose b8e500 b8e252
            | (have j0 := b8e252 X0 X1
               have j1 := b8e500 X0 X1
               grind)
            | (have r₁ := b8e252 X0 X1
               have r₂ := b8e500 X0 X1
               grind)
            | exact resolve b8e252 b8e500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e252 b8e500
          have b8e8203 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e8014 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8014
          have b8e13072 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2290 (τ X1) (τ X0)
               have i₂ := b8e41 X0 X1
               grind)
            | exact superpose b8e41 b8e2290
            | (have j0 := b8e2290 (τ X0) (τ X1)
               grind)
            | exact resolve b8e2290 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2290
          have b8e13157 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13072 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13072
            | (have j0 := b8e13072 X0 X1
               grind)
            | exact resolve b8e13072 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13072
          have b8e13190 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13157 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e13157
            | (have j0 := b8e13157 X0 X1
               grind)
            | exact resolve b8e13157 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13157
          have b8e13212 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13190 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13190
            | (have j0 := b8e13190 X0 X1
               grind)
            | exact resolve b8e13190 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13190
          have b8e13228 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13212 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e13212
            | (have j0 := b8e13212 X0 X1
               grind)
            | exact resolve b8e13212 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13212
          have b8e13237 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13228 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e13228
            | (have j0 := b8e13228 X0 X1
               grind)
            | exact resolve b8e13228 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13228
          have b8e13242 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13237 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e13237
            | (have j0 := b8e13237 X0 X1
               grind)
            | exact resolve b8e13237 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13237
          have b8e13243 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13242 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e13242
            | (have j0 := b8e13242 X0 X1
               grind)
            | exact resolve b8e13242 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13242
          have b8e22908 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2079 (τ X1) (τ X0)
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e2079
            | (have j0 := b8e2079 (τ X1) (τ X0)
               grind)
            | exact resolve b8e2079 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2079
          have b8e23018 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22908 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e22908
            | (have j0 := b8e22908 X0 X1
               grind)
            | exact resolve b8e22908 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22908
          have b8e23065 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23018 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e23018
            | (have j0 := b8e23018 X0 X1
               grind)
            | exact resolve b8e23018 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23018
          have b8e23101 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23065 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e23065
            | (have j0 := b8e23065 X0 X1
               grind)
            | exact resolve b8e23065 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23065
          have b8e23130 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23101 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e23101
            | (have j0 := b8e23101 X0 X1
               grind)
            | exact resolve b8e23101 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23101
          have b8e23155 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23130 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e23130
            | (have j0 := b8e23130 X0 X1
               grind)
            | exact resolve b8e23130 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23130
          have b8e23178 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23155 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e23155
            | (have j0 := b8e23155 X0 X1
               grind)
            | exact resolve b8e23155 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23155
          have b8e23195 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23178 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e23178
            | (have j0 := b8e23178 X0 X1
               grind)
            | exact resolve b8e23178 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23178
          have b8e23208 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e23195 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e23195
            | (have j0 := b8e23195 X0 X1
               grind)
            | exact resolve b8e23195 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23195
          have b8e23690 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2080 (τ X1) (τ X0)
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e2080
            | (have j0 := b8e2080 (τ X1) (τ X0)
               grind)
            | exact resolve b8e2080 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2080
          have b8e23801 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23690 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e23690
            | (have j0 := b8e23690 X0 X1
               grind)
            | exact resolve b8e23690 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23690
          have b8e23846 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23801 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e23801
            | (have j0 := b8e23801 X0 X1
               grind)
            | exact resolve b8e23801 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23801
          have b8e23882 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23846 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e23846
            | (have j0 := b8e23846 X0 X1
               grind)
            | exact resolve b8e23846 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23846
          have b8e23911 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23882 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e23882
            | (have j0 := b8e23882 X0 X1
               grind)
            | exact resolve b8e23882 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23882
          have b8e23936 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23911 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e23911
            | (have j0 := b8e23911 X0 X1
               grind)
            | exact resolve b8e23911 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23911
          have b8e23957 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23936 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e23936
            | (have j0 := b8e23936 X0 X1
               grind)
            | exact resolve b8e23936 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23936
          have b8e23974 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23957 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e23957
            | (have j0 := b8e23957 X0 X1
               grind)
            | exact resolve b8e23957 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23957
          have b8e23987 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e23974 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e23974
            | (have j0 := b8e23974 X0 X1
               grind)
            | exact resolve b8e23974 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23974
          have b8e89661 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 (τ X1)
               have i₂ := b8e8203 X1 (τ X0)
               grind)
            | exact superpose b8e8203 b8e26
            | (have j1 := b8e8203 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e8203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e90074 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e8203 (σ X0) X1
               grind)
            | exact superpose b8e8203 b8e38
            | (have j1 := b8e8203 (σ X0) X1
               grind)
            | exact resolve b8e38 b8e8203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8203
          have b8e90518 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e90074 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e90074
            | (have j0 := b8e90074 X0 X1
               grind)
            | exact resolve b8e90074 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90074
          have b8e90673 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e89661 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e89661
            | (have j0 := b8e89661 X0 X1
               grind)
            | exact resolve b8e89661 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89661
          have b8e91022 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e90518 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e90518
            | (have j0 := b8e90518 X0 X1
               grind)
            | exact resolve b8e90518 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90518
          have b8e91098 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e90673 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e90673
            | (have j0 := b8e90673 X0 X1
               grind)
            | exact resolve b8e90673 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e90673
          have b8e91313 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e91022 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e91022
            | (have j0 := b8e91022 X0 X1
               grind)
            | exact resolve b8e91022 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91022
          have b8e91370 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e91098 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e91098
            | (have j0 := b8e91098 X0 X1
               grind)
            | exact resolve b8e91098 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91098
          have b8e91513 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e91313 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e91313
            | (have j0 := b8e91313 X0 X1
               grind)
            | exact resolve b8e91313 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91313
          have b8e91557 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e91370 X0 X1
               have i₂ := b8e41 X0 X1
               grind)
            | exact superpose b8e41 b8e91370
            | (have j0 := b8e91370 X0 X1
               grind)
            | exact resolve b8e91370 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e91370
          have b8e91616 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e91513 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e91513
            | (have j0 := b8e91513 X0 X1
               grind)
            | exact resolve b8e91513 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91513
          have b8e93259 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 X1
               have i₂ := b8e91616 (σ X0) X1
               grind)
            | exact superpose b8e91616 b8e38
            | (have j1 := b8e91616 (σ X0) X1
               grind)
            | exact resolve b8e38 b8e91616
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91616
          have b8e93649 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e93259 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e93259
            | (have j0 := b8e93259 X0 X1
               grind)
            | exact resolve b8e93259 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93259
          have b8e94329 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e93649 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e93649
            | (have j0 := b8e93649 X0 X1
               grind)
            | exact resolve b8e93649 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93649
          have b8e106827 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13243 X1 X0
               have i₂ := b8e91557 X0 X1
               grind)
            | exact superpose b8e91557 b8e13243
            | (have j0 := b8e13243 X0 X1
               have j1 := b8e91557 X1 X0
               grind)
            | (have r₁ := b8e13243 X1 X0
               have r₂ := b8e91557 X0 X1
               grind)
            | (have r₁ := b8e13243 X1 X1
               have r₂ := b8e91557 X1 X1
               grind)
            | exact resolve b8e13243 b8e91557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e107405 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e23208 X1 X0
               have i₂ := b8e91557 X0 X1
               grind)
            | exact superpose b8e91557 b8e23208
            | (have j0 := b8e23208 X1 X0
               have j1 := b8e91557 X0 X1
               grind)
            | (have r₁ := b8e23208 X1 X1
               have r₂ := b8e91557 X1 X1
               grind)
            | (have r₁ := b8e23208 X1 X0
               have r₂ := b8e91557 X0 X1
               grind)
            | exact resolve b8e23208 b8e91557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23208
          have b8e107589 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e91557 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e107590 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e91557 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91557
          have b8e107594 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e107405 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107405
          have b8e107663 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e106827 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106827
          have b8e108210 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e107594 X0 X1
               have j1 := b8e23987 X1 X0
               grind)
            | (have r₁ := b8e107594 X1 X0
               have r₂ := b8e23987 X0 X1
               grind)
            | exact resolve b8e107594 b8e23987
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23987 b8e107594
          have b8e108494 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e107663 X0 X1
               have j1 := b8e107589 X0 X1
               grind)
            | (have r₁ := b8e107663 X0 X1
               have r₂ := b8e107589 X0 X1
               grind)
            | (have r₁ := b8e107663 X1 X0
               have r₂ := b8e107589 X0 X1
               grind)
            | (have r₁ := b8e107663 X1 X1
               have r₂ := b8e107589 X1 X1
               grind)
            | exact resolve b8e107663 b8e107589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107589 b8e107663
          have b8e145322 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e108210 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e108210 X0 X1
               grind)
            | exact superpose b8e108210 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e108210 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e108210 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e108210 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e108210 X0 X0
               grind)
            | exact resolve b8e17 b8e108210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108210
          have b8e146629 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e145322 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145322
          have b8e146958 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e146629 X0 X1
               have j1 := b8e107590 X1 X0
               grind)
            | (have r₁ := b8e146629 X0 X1
               have r₂ := b8e107590 X0 X1
               grind)
            | (have r₁ := b8e146629 X1 X0
               have r₂ := b8e107590 X0 X1
               grind)
            | (have r₁ := b8e146629 X1 X1
               have r₂ := b8e107590 X1 X1
               grind)
            | exact resolve b8e146629 b8e107590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107590 b8e146629
          have b8e147684 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e108494 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e108494
            | (have j0 := b8e108494 (σ X0) X1
               grind)
            | exact resolve b8e108494 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108494
          have b8e149358 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e147684 X0 X1
               have i₂ := b8e38 X0 X1
               grind)
            | exact superpose b8e38 b8e147684
            | (have j0 := b8e147684 X0 X1
               grind)
            | exact resolve b8e147684 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147684
          have b8e171124 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e146958 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e146958
            | (have j0 := b8e146958 (σ X0) X1
               grind)
            | exact resolve b8e146958 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146958
          have b8e172966 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e171124 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e171124
            | (have j0 := b8e171124 X0 X1
               grind)
            | exact resolve b8e171124 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171124
          have b8e203198 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e94329 X1 (σ X0)
               grind)
            | exact superpose b8e94329 b8e30
            | (have j1 := b8e94329 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e94329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94329
          have b8e203209 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e203198 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e203198
            | (have j0 := b8e203198 X0 X1
               grind)
            | exact resolve b8e203198 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203198
          have b8e203251 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e203209 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e203209
            | (have j0 := b8e203209 X0 X1
               grind)
            | exact resolve b8e203209 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203209
          have b8e203281 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e203251 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e203251
            | (have j0 := b8e203251 X0 X1
               grind)
            | exact resolve b8e203251 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203251
          have b8e203302 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e203281 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e203281
            | (have j0 := b8e203281 X0 X1
               grind)
            | exact resolve b8e203281 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203281
          have b8e203314 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e203302 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e203302
            | (have j0 := b8e203302 X0 X1
               grind)
            | exact resolve b8e203302 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203302
          have b8e207952 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e203314 x y
               grind)
            | exact superpose b8e203314 b8e20
            | (have j1 := b8e203314 x y
               grind)
            | exact resolve b8e20 b8e203314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203314
          have b8e210122 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e207952
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e207952
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e207952 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e210127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e207952
               have i₂ := b8e7650 x y
               grind)
            | exact superpose b8e7650 b8e207952
            | (have j1 := b8e7650 x y
               grind)
            | (have r₁ := b8e207952
               have r₂ := b8e7650 x y
               grind)
            | exact resolve b8e207952 b8e7650
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7650 b8e207952
          have b8e210134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e210127
          have b8e210135 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e210134
          have b8e210140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e210122
          have b8e210141 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e210140
          have b8e210143 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e210135
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e210135 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210135
          have b8e212819 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e13243 y x
               have i₂ := b8e210143
               grind)
            | exact superpose b8e210143 b8e13243
            | (have j0 := b8e13243 y x
               grind)
            | (have r₁ := b8e13243 y x
               have r₂ := b8e210143
               grind)
            | exact resolve b8e13243 b8e210143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13243
          have b8e212837 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
          clear b8e210143
          have b8e212841 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e212819
          have b8e212858 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e212841
               have r₂ := b8e212837
               grind)
            | exact resolve b8e212841 b8e212837
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212837 b8e212841
          have b8e259033 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e149358 X1 (σ X0)
               grind)
            | exact superpose b8e149358 b8e30
            | (have j1 := b8e149358 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e149358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e149358
          have b8e259038 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e259033 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e259033
            | (have j0 := b8e259033 X0 X1
               grind)
            | exact resolve b8e259033 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259033
          have b8e259052 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e259038 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e259038
            | (have j0 := b8e259038 X0 X1
               grind)
            | exact resolve b8e259038 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259038
          have b8e259059 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e259052 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e259052
            | (have j0 := b8e259052 X0 X1
               grind)
            | exact resolve b8e259052 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259052
          have b8e259063 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e259059 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e259059
            | (have j0 := b8e259059 X0 X1
               grind)
            | exact resolve b8e259059 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259059
          have b8e259064 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e259063 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e259063
            | (have j0 := b8e259063 X0 X1
               grind)
            | exact resolve b8e259063 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259063
          have b8e259543 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e259064 x y
               grind)
            | exact superpose b8e259064 b8e20
            | (have j1 := b8e259064 x y
               grind)
            | exact resolve b8e20 b8e259064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259064
          have b8e293134 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e172966 X1 (σ X0)
               grind)
            | exact superpose b8e172966 b8e38
            | (have j1 := b8e172966 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e172966
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e172966
          have b8e293139 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e293134 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e293134
            | (have j0 := b8e293134 X0 X1
               grind)
            | exact resolve b8e293134 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293134
          have b8e293157 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e293139 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e293139
            | (have j0 := b8e293139 X0 X1
               grind)
            | exact resolve b8e293139 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293139
          have b8e293168 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e293157 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e293157
            | (have j0 := b8e293157 X0 X1
               grind)
            | exact resolve b8e293157 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293157
          have b8e293174 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e293168 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e293168
            | (have j0 := b8e293168 X0 X1
               grind)
            | exact resolve b8e293168 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293168
          have b8e293175 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e293174 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e293174
            | (have j0 := b8e293174 X0 X1
               grind)
            | exact resolve b8e293174 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73 b8e293174
          have b8e293709 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e293175 y x
               grind)
            | exact superpose b8e293175 b8e20
            | (have j1 := b8e293175 y x
               grind)
            | exact resolve b8e20 b8e293175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293175
          have b8e293902 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e293709
               have i₂ := b8e210141
               grind)
            | exact superpose b8e210141 b8e293709
            | exact resolve b8e293709 b8e210141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210141 b8e293709
          have b8e293903 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e293902
          have b8e293904 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e293903
          have b8e294145 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e212858
               have i₂ := b8e293904
               grind)
            | exact superpose b8e293904 b8e212858
            | exact resolve b8e212858 b8e293904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212858 b8e293904
          have b8e294178 : (M.op x y) = (M.op x x) := by grind
          clear b8e294145
          have b8e295457 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e259543
               have i₂ := b8e294178
               grind)
            | exact superpose b8e294178 b8e259543
            | exact resolve b8e259543 b8e294178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259543
          have b8e295460 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e294178
               grind)
            | exact superpose b8e294178 b8e17
            | (have j0 := b8e17 x x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e294178
               grind)
            | exact resolve b8e17 b8e294178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e295524 : (M.op y y) = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
          clear b8e295460
          have b8e295525 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b8e295457
          have b8e295526 : (M.op x x) = (k y x) := by grind
          clear b8e295525
          have b8e296943 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e2078 x y
               have i₂ := b8e295526
               grind)
            | exact superpose b8e295526 b8e2078
            | (have j0 := b8e2078 x y
               grind)
            | exact resolve b8e2078 b8e295526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2078
          have b8e296973 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e296943
          have b8e298627 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b8e295526
               have i₂ := b8e295524
               grind)
            | exact superpose b8e295524 b8e295526
            | exact resolve b8e295526 b8e295524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e295524 b8e295526
          have b8e298679 : (M.op x x) = (M.op y y) := by grind
          clear b8e298627
          have b8e339750 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e296973
               have i₂ := b8e298679
               grind)
            | exact superpose b8e298679 b8e296973
            | exact resolve b8e296973 b8e298679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e296973 b8e298679
          have b8e339752 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e339750
          have b8e341761 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e339752
               grind)
            | exact superpose b8e339752 b8e20
            | exact resolve b8e20 b8e339752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e339752
          have b8e341829 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e341761
               have i₂ := b8e294178
               grind)
            | exact superpose b8e294178 b8e341761
            | exact resolve b8e341761 b8e294178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e294178 b8e341761
          have b8e341830 : False := by grind
          exact b8e341830

/-- `Equation2887`: `x = ((x ◇ (y ◇ z)) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation2887 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2887 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2887.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e78 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e84 : False := by grind
      exact b0e84
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : (M.op x x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x x)) y) y) = X0 := by
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
          have b4e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) X1 X2
               have i₂ := b4e13 X0 (M.op X1 X2) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e139 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x x) X1)) (M.op x x)) = (M.op (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 (M.op (M.op X0 (M.op (M.op x x) X1)) (M.op x x))
               have i₂ := b4e13 X0 (M.op x x) X1
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e141 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 x) x) := by
            intro X0
            first
            | (have i₁ := b4e139 X0 x
               have i₂ := b4e41 X0 x x x
               grind)
            | exact superpose b4e41 b4e139
            | exact resolve b4e139 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139
          have b4e209 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op X1 X2) x
               have i₂ := b4e41 X0 X1 X2 x
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e398 : ∀ X0 : G, y = (M.op (M.op (M.op x x) y) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e209 y y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e209
            | exact resolve b4e209 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e399 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e209 (M.op X0 (M.op X1 X3)) X1 X2
               have i₂ := b4e13 X0 X1 X3
               grind)
            | exact superpose b4e13 b4e209
            | exact resolve b4e209 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e400 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e209 (M.op X0 (M.op x x)) y X1
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e209
            | exact resolve b4e209 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e434 : y = (M.op (M.op (M.op x x) y) (M.op x x)) := by
            first
            | (have i₁ := b4e398 x
               have i₂ := b4e400 (M.op (M.op x x) y) x
               grind)
            | exact superpose b4e400 b4e398
            | exact resolve b4e398 b4e400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e398 b4e400
          have b4e884 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (M.op X0 X2) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e399 X1 (M.op (M.op X0 X2) X2) X3 (M.op X2 x)
               have i₂ := b4e209 X0 X2 x
               grind)
            | exact superpose b4e209 b4e399
            | exact resolve b4e399 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e888 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 x) x)) = (M.op X1 (M.op (M.op X0 y) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e399 X1 (M.op X0 y) X2 y
               have i₂ := b4e141 X0
               grind)
            | exact superpose b4e141 b4e399
            | exact resolve b4e399 b4e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141
          have b4e1471 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x x) y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e399 X0 (M.op (M.op x x) y) X1 (M.op x x)
               have i₂ := b4e434
               grind)
            | exact superpose b4e434 b4e399
            | exact resolve b4e399 b4e434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e399
          have b4e1475 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x x) x) x)) := by
            intro X0
            first
            | (have i₁ := b4e1471 X0 x
               have i₂ := b4e888 (M.op x x) X0 x
               grind)
            | exact superpose b4e888 b4e1471
            | exact resolve b4e1471 b4e888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e888 b4e1471
          have b4e1486 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e1475 X0
               have i₂ := b4e884 x X0 x x
               grind)
            | exact superpose b4e884 b4e1475
            | exact resolve b4e1475 b4e884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e884 b4e1475
          have b4e1688 : y = (M.op (M.op (M.op x x) x) (M.op x x)) := by
            first
            | (have i₁ := b4e434
               have i₂ := b4e1486 (M.op x x)
               grind)
            | exact superpose b4e1486 b4e434
            | exact resolve b4e434 b4e1486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e434 b4e1486
          have b4e1712 : x = y := by
            first
            | (have i₁ := b4e1688
               have i₂ := b4e209 x x x
               grind)
            | exact superpose b4e209 b4e1688
            | exact resolve b4e1688 b4e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209 b4e1688
          have b4e1734 : False := by grind
          exact b4e1734
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b5e56 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e56
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e56
            | exact resolve b5e56 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e59 : False := by grind
          exact b5e59
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
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b7e58 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e58
            | exact resolve b7e58 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e58
          have b7e72 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e60
               grind)
            | exact superpose b7e60 b7e14
            | exact resolve b7e14 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e73 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e72
            | exact resolve b7e72 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e77 : False := by grind
          exact b7e77
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
          have b8e55 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e57 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e55
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e55
            | exact resolve b8e55 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e86 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e22
               have i₂ := b8e18 X0 y
               grind)
            | (have i₁ := b8e22
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e22
            | (have j1 := b8e18 X0 y
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
          have b8e89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e69 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e69
            | (have j0 := b8e69 X0 X1
               grind)
            | exact resolve b8e69 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e89
            | (have j0 := b8e89 X0 X1
               grind)
            | exact resolve b8e89 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e89
          have b8e154 : (M.op x y) = (k x y) ∨ x = y := by
            first
            | (have j0 := b8e86 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e155 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e154
               have r₂ := b8e21
               grind)
            | exact resolve b8e154 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154
          have b8e568 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e91 x y
               grind)
            | exact superpose b8e91 b8e20
            | (have j1 := b8e91 y x
               grind)
            | exact resolve b8e20 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e613 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e568
               have r₂ := b8e57
               grind)
            | exact resolve b8e568 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57 b8e568
          have b8e629 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e613
               have r₂ := b8e23
               grind)
            | exact resolve b8e613 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e613
          have b8e640 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e629
               have i₂ := b8e155
               grind)
            | exact superpose b8e155 b8e629
            | exact resolve b8e629 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155 b8e629
          have b8e641 : False := by grind
          exact b8e641

/-- `Equation3475`: `x ◇ x = y ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3475 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3475 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3475.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e82 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e85 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e82 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e107 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e85 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e85
        | exact resolve b0e85 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e108 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e85 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e85
        | exact resolve b0e85 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e111 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e107
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e107
        | exact resolve b0e107 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107
      have b0e112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e111
           have i₂ := b0e108
           grind)
        | exact superpose b0e108 b0e111
        | exact resolve b0e111 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108 b0e111
      have b0e113 : False := by grind
      exact b0e113
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e35 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e37 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e35
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e35
          | exact resolve b1e35 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e76 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e76 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e94 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e37
             grind)
          | exact superpose b1e37 b1e19
          | exact resolve b1e19 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e131 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e79 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e79
          | exact resolve b1e79 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e137 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e94
             have i₂ := b1e131
             grind)
          | exact superpose b1e131 b1e94
          | exact resolve b1e94 b1e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94 b1e131
        have b1e139 : False := by grind
        exact b1e139
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e73 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e487 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e73 X0
             have i₂ := b2e48 X0 X1
             grind)
          | (have i₁ := b2e73 X0
             have i₂ := b2e48 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e48 b2e73
          | (have j1 := b2e48 X1 X0
             grind)
          | exact resolve b2e73 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e73
        have b2e513 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e487 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e487
        have b2e682 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e513 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e513
        have b2e683 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e682 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e682
        have b2e714 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e683 (σ X0)
             grind)
          | exact superpose b2e683 b2e18
          | exact resolve b2e18 b2e683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e722 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e714 X0
             have i₂ := b2e683 X0
             grind)
          | exact superpose b2e683 b2e714
          | exact resolve b2e714 b2e683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e683 b2e714
        have b2e1003 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e722 x
             grind)
          | exact superpose b2e722 b2e21
          | exact resolve b2e21 b2e722
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e722
        have b2e1031 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1003
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1003
          | exact resolve b2e1003 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1003
        have b2e1032 : False := by grind
        exact b2e1032
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e34 : (M.op x y) = (k y x) := by grind
        have b3e67 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e81 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e67
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e67
          | exact resolve b3e67 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e82 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e81
          | exact resolve b3e81 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e83 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e82
             have r₂ := b3e19
             grind)
          | exact resolve b3e82 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e91 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e83
        have b3e93 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e91
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e91
          | exact resolve b3e91 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e94 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e93
          | exact resolve b3e93 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e93
        have b3e95 : False := by grind
        exact b3e95
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e40 : (M.op x y) = (k y x) := by grind
          have b4e41 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e44 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e41
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e41
            | exact resolve b4e41 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e45 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e44
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e44
            | exact resolve b4e44 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e44
          have b4e46 : False := by grind
          exact b4e46
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e482 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e84 X0
               have i₂ := b5e55 X0 X1
               grind)
            | (have i₁ := b5e84 X0
               have i₂ := b5e55 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e55 b5e84
            | (have j1 := b5e55 X1 X0
               grind)
            | exact resolve b5e84 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e84
          have b5e506 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e482 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e482
          have b5e671 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e506 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e506
          have b5e672 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e671 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e671
          have b5e702 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e672 (σ X0)
               grind)
            | exact superpose b5e672 b5e19
            | exact resolve b5e19 b5e672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e710 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e702 X0
               have i₂ := b5e672 X0
               grind)
            | exact superpose b5e672 b5e702
            | exact resolve b5e702 b5e672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e672 b5e702
          have b5e987 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e710 y
               grind)
            | exact superpose b5e710 b5e24
            | exact resolve b5e24 b5e710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e710
          have b5e1014 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e987
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e987
            | exact resolve b5e987 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e987
          have b5e1015 : False := by grind
          exact b5e1015
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e77 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e593 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e80 X0
             have i₂ := b6e60 X0 X1
             grind)
          | (have i₁ := b6e80 X0
             have i₂ := b6e60 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e60 b6e80
          | (have j1 := b6e60 X1 X0
             grind)
          | exact resolve b6e80 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e80
        have b6e616 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e593 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e593
        have b6e830 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e616 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e616
        have b6e831 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e830 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e830
        have b6e961 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e831 (σ X0)
             grind)
          | exact superpose b6e831 b6e18
          | exact resolve b6e18 b6e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e968 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e961 X0
             have i₂ := b6e831 X0
             grind)
          | exact superpose b6e831 b6e961
          | exact resolve b6e961 b6e831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e831 b6e961
        have b6e1269 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e968 x
             grind)
          | exact superpose b6e968 b6e22
          | exact resolve b6e22 b6e968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e968
        have b6e1467 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e1269
             grind)
          | exact superpose b6e1269 b6e13
          | exact resolve b6e13 b6e1269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1269
        have b6e1468 : y = (M.op x x) := by
          first
          | (have i₁ := b6e1467
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1467
          | exact resolve b6e1467 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1467
        have b6e1474 : False := by grind
        exact b6e1474
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e85 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e88 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e85 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e377 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e88 X0
               have i₂ := b7e60 X0 X1
               grind)
            | (have i₁ := b7e88 X0
               have i₂ := b7e60 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e60 b7e88
            | (have j1 := b7e60 X1 X0
               grind)
            | exact resolve b7e88 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e88
          have b7e397 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e377 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e377
          have b7e426 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e397 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e397
          have b7e522 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e426 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e426
            | exact resolve b7e426 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e529 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e426 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e426
          have b7e536 : (σ x) = (k (σ y) (σ y)) := by grind
          clear b7e522
          have b7e547 : (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e536
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e536
            | exact resolve b7e536 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e536
          have b7e554 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e547
               have i₂ := b7e529 y
               grind)
            | exact superpose b7e529 b7e547
            | exact resolve b7e547 b7e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e529 b7e547
          have b7e631 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e554
               grind)
            | exact superpose b7e554 b7e14
            | exact resolve b7e14 b7e554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e554
          have b7e632 : x = (M.op y y) := by
            first
            | (have i₁ := b7e631
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e631
            | exact resolve b7e631 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e631
          have b7e637 : False := by grind
          exact b7e637
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
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e466 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e467 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e466
               have r₂ := b8e24
               grind)
            | exact resolve b8e466 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e466
          have b8e468 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e467
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e467
            | exact resolve b8e467 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e467
          have b8e508 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e20
            | exact resolve b8e20 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e468
          have b8e654 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e508
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e508
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e508 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e508
          have b8e657 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e654
          have b8e658 : x = (M.op y y) := by
            first
            | (have r₁ := b8e657
               have r₂ := b8e21
               grind)
            | exact resolve b8e657 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e657
          have b8e659 : False := by grind
          exact b8e659
