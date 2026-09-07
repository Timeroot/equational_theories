import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pxy_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e75 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e79 : False := by grind
      exact b0e79
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
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
          have b4e43 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e13 X0 y y
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e47 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e48 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e47 X0
               have i₂ := b4e13 X0 (σ y) (σ y)
               grind)
            | exact superpose b4e13 b4e47
            | exact resolve b4e47 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e108 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e48 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e48
            | exact resolve b4e48 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e48
          have b4e112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e108
               have i₂ := b4e43 x
               grind)
            | exact superpose b4e43 b4e108
            | exact resolve b4e108 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e108
          have b4e114 : False := by grind
          exact b4e114
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) X0)) := by
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
          have b5e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X3 X1) X0) X0
               have i₂ := b5e13 X0 X1 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e40 X0 X1 X2 X3
               have i₂ := b5e13 X2 X1 X0
               grind)
            | exact superpose b5e13 b5e40
            | exact resolve b5e40 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e43 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e39 X0
               have i₂ := b5e13 X0 y y
               grind)
            | exact superpose b5e13 b5e39
            | exact resolve b5e39 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e81 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e80 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e77 X0 X1
               have i₂ := b5e30 X1
               grind)
            | exact superpose b5e30 b5e77
            | (have j0 := b5e77 X0 X1
               grind)
            | exact resolve b5e77 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e406 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e82 y x
               grind)
            | exact superpose b5e82 b5e20
            | (have j1 := b5e82 y x
               grind)
            | exact resolve b5e20 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e443 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e406
               have r₂ := b5e23
               grind)
            | exact resolve b5e406 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e406
          have b5e464 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e443
               have i₂ := b5e43 x
               grind)
            | exact superpose b5e43 b5e443
            | exact resolve b5e443 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e443
          have b5e465 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
          clear b5e464
          have b5e490 : (M.op (σ y) (σ y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e465
               grind)
            | exact superpose b5e465 b5e24
            | exact resolve b5e24 b5e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e495 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (k y x)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 X1 (σ x) X0 (σ y)
               have i₂ := b5e465
               grind)
            | exact superpose b5e465 b5e42
            | exact resolve b5e42 b5e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e503 : (σ (M.op y y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e490
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e490
            | exact resolve b5e490 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e490
          have b5e550 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e503
               have i₂ := b5e81 x y
               grind)
            | exact superpose b5e81 b5e503
            | (have j1 := b5e81 x y
               grind)
            | (have r₁ := b5e503
               have r₂ := b5e81 (σ (M.op y y)) (σ (k y x))
               grind)
            | (have r₁ := b5e503
               have r₂ := b5e81 (σ (k y x)) (σ (M.op y y))
               grind)
            | exact resolve b5e503 b5e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81 b5e503
          have b5e552 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b5e550
               have r₂ := b5e21
               grind)
            | exact resolve b5e550 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e550
          have b5e553 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e552
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e552
            | exact resolve b5e552 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e552
          have b5e554 : y = (k y x) := by grind
          clear b5e553
          have b5e934 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e495 X0 X1
               have i₂ := b5e554
               grind)
            | exact superpose b5e554 b5e495
            | exact resolve b5e495 b5e554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e495
          have b5e1200 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (k y x))) := by
            intro X0
            first
            | (have i₁ := b5e934 X0 (σ x)
               have i₂ := b5e465
               grind)
            | exact superpose b5e465 b5e934
            | exact resolve b5e934 b5e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e465 b5e934
          have b5e1260 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e1200 X0
               have i₂ := b5e554
               grind)
            | exact superpose b5e554 b5e1200
            | exact resolve b5e1200 b5e554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e554 b5e1200
          have b5e1350 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1260 (σ y)
               grind)
            | exact superpose b5e1260 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1260 (σ y)
               grind)
            | exact resolve b5e24 b5e1260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1260
          have b5e1358 : False := by grind
          exact b5e1358
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X3 X1) X0) X0
               have i₂ := b7e13 X0 X1 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e39 X0 X1 X2 X3
               have i₂ := b7e13 X2 X1 X0
               grind)
            | exact superpose b7e13 b7e39
            | exact resolve b7e39 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e60 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e63 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e60
          have b7e64 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e23
               grind)
            | exact resolve b7e63 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e65 : (σ x) = (σ (k x y)) := by
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
          have b7e68 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69 : x = (k x y) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e68
            | exact resolve b7e68 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e87 : (σ (M.op x y)) = (σ x) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e65
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e65 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e90 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e22
               grind)
            | exact resolve b7e87 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e97 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e21
               grind)
            | exact resolve b7e90 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e99 : x = (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e100 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e22
               grind)
            | exact resolve b7e99 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e102 : x = (M.op x y) := by
            first
            | (have r₁ := b7e100
               have r₂ := b7e21
               grind)
            | exact resolve b7e100 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e115 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e13
            | exact resolve b7e13 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e123 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e41 X1 y X0 x
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e41
            | exact resolve b7e41 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e146 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b7e30 (M.op x y)
               have i₂ := b7e97
               grind)
            | exact superpose b7e97 b7e30
            | exact resolve b7e30 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e153 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b7e146
               have i₂ := b7e123 (M.op x y) y
               grind)
            | exact superpose b7e123 b7e146
            | exact resolve b7e146 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123 b7e146
          have b7e154 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e153
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e153
            | exact resolve b7e153 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102 b7e153
          have b7e155 : (σ (M.op x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e154
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e154
            | exact resolve b7e154 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e154
          have b7e156 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e155
               have i₂ := b7e97
               grind)
            | exact superpose b7e97 b7e155
            | exact resolve b7e155 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e155
          have b7e168 : (τ (σ x)) = (M.op x x) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e156
               grind)
            | exact superpose b7e156 b7e14
            | exact resolve b7e14 b7e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e169 : x = (M.op x x) := by
            first
            | (have i₁ := b7e168
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e168
            | exact resolve b7e168 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e168
          have b7e248 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x x
               have i₂ := b7e169
               grind)
            | exact superpose b7e169 b7e13
            | exact resolve b7e13 b7e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e169
          have b7e249 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e248 X0
               have i₂ := b7e115 X0
               grind)
            | exact superpose b7e115 b7e248
            | exact resolve b7e248 b7e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115 b7e248
          have b7e330 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e249 y
               grind)
            | exact superpose b7e249 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e249 y
               grind)
            | exact resolve b7e22 b7e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e249
          have b7e331 : False := by grind
          exact b7e331
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e84
            | (have j0 := b8e84 X0 X1
               grind)
            | exact resolve b8e84 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e445 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
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
          have b8e504 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e445
               have r₂ := b8e23
               grind)
            | exact resolve b8e445 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e445
          have b8e1200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e504
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e504
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e504
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e504
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e504 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e1201 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by grind
          clear b8e1200
          have b8e1206 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have r₁ := b8e1201
               have r₂ := b8e22
               grind)
            | exact resolve b8e1201 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1201
          have b8e1211 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1206
               have r₂ := b8e21
               grind)
            | exact resolve b8e1206 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1206
          have b8e1216 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e1211
               grind)
            | exact superpose b8e1211 b8e24
            | exact resolve b8e24 b8e1211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1211
          have b8e1242 : False := by grind
          exact b8e1242

/-- `Equation3541`: `x ◇ y = x ◇ ((z ◇ w) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pxy_Equation3541 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3541 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3541.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e81 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e85 : False := by grind
      exact b0e85
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e31
          have b4e60 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e27
            | (have r₁ := b4e27
               have r₂ := b4e32 x
               grind)
            | exact resolve b4e27 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e32
          have b4e62 : False := by grind
          exact b4e62
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e59 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) := by
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
          have b5e60 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X2 X3) X1) = X0 ∨ (k X0 (M.op (M.op X2 X3) X1)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e17 X0 (M.op (M.op X2 X3) X1)
               have i₂ := b5e13 X0 X1 X2 X3
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 X0 X1
               grind)
            | (have r₁ := b5e17 (M.op (M.op X2 X3) X1) X1
               have r₂ := b5e13 (M.op (M.op X2 X3) X1) X1 X2 X3
               grind)
            | (have r₁ := b5e17 X1 (M.op (M.op X2 X3) X1)
               have r₂ := b5e13 X1 X1 X2 X3
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e64 : x = y ∨ x = (k x y) := by grind
          clear b5e59
          have b5e65 : x = (k x y) := by
            first
            | (have r₁ := b5e64
               have r₂ := b5e21
               grind)
            | exact resolve b5e64 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e70 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ X0 = X2 ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X0 X1
               have i₂ := b5e18 X0 X2
               grind)
            | (have i₁ := b5e18 X1 X1
               have i₂ := b5e18 X1 X1
               grind)
            | exact superpose b5e18 b5e18
            | (have j0 := b5e18 X0 X2
               have j1 := b5e18 X0 X2
               grind)
            | exact resolve b5e18 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e84 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X0
               have i₂ := b5e18 (σ X0) X1
               grind)
            | (have i₁ := b5e31 X0
               have i₂ := b5e18 (σ X0) (σ X0)
               grind)
            | exact superpose b5e18 b5e31
            | (have j1 := b5e18 (σ X0) X1
               grind)
            | exact resolve b5e31 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0 X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e73
            | (have j0 := b5e73 X0 X1
               grind)
            | exact resolve b5e73 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e133 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X1) X2)) = X2 ∨ (M.op (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e60 X2 X2 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e444 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e90 x y
               grind)
            | exact superpose b5e90 b5e24
            | (have j1 := b5e90 x y
               grind)
            | exact resolve b5e24 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e499 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e444
               have r₂ := b5e26
               grind)
            | exact resolve b5e444 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e444
          have b5e521 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b5e499
               have r₂ := b5e23
               grind)
            | exact resolve b5e499 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e499
          have b5e532 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e521
               have i₂ := b5e65
               grind)
            | exact superpose b5e65 b5e521
            | exact resolve b5e521 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e521
          have b5e538 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e532
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e532
            | exact resolve b5e532 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e532
          have b5e626 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e26
               have i₂ := b5e70 (σ x) (σ y) X0
               grind)
            | (have i₁ := b5e26
               have i₂ := b5e70 (σ x) X0 (σ y)
               grind)
            | exact superpose b5e70 b5e26
            | (have j1 := b5e70 (σ x) (σ y) (σ y)
               grind)
            | (have r₁ := b5e26
               have r₂ := b5e70 (M.op (σ x) (σ y)) x (σ (M.op x x))
               grind)
            | (have r₁ := b5e26
               have r₂ := b5e70 (σ (M.op x x)) x (M.op (σ x) (σ y))
               grind)
            | (have r₁ := b5e26
               have r₂ := b5e70 (M.op (σ x) (σ y)) (σ (M.op x x)) x
               grind)
            | exact resolve b5e26 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e70
          have b5e661 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have j0 := b5e626 X0
               grind)
            | (have r₁ := b5e626 X0
               have r₂ := b5e23
               grind)
            | (have r₁ := b5e626 (σ y)
               have r₂ := b5e23
               grind)
            | exact resolve b5e626 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e626
          have b5e676 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have j0 := b5e661 X0
               have j1 := b5e84 x X0
               grind)
            | (have r₁ := b5e661 x
               have r₂ := b5e84 x x
               grind)
            | (have r₁ := b5e661 X0
               have r₂ := b5e84 (M.op x x) (M.op (σ x) X0)
               grind)
            | exact resolve b5e661 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e661
          have b5e684 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e676 X0
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e676
            | (have j0 := b5e676 X0
               grind)
            | exact resolve b5e676 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e676
          have b5e692 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e684 X0
               have i₂ := b5e65
               grind)
            | exact superpose b5e65 b5e684
            | (have j0 := b5e684 X0
               grind)
            | exact resolve b5e684 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e684
          have b5e3554 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 X1) (σ x))) ∨ (σ x) = (M.op (M.op X0 X1) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op X0 X1) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e133 X0 X1 (σ x)
               have i₂ := b5e692 (M.op (M.op X0 X1) (σ x))
               grind)
            | exact superpose b5e692 b5e133
            | (have j0 := b5e133 X0 X1 (σ x)
               have j1 := b5e692 (M.op (σ x) (M.op (M.op X0 X1) (σ x)))
               grind)
            | exact resolve b5e133 b5e692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133 b5e692
          have b5e3589 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 X1) (σ x))) ∨ (σ x) = (M.op (M.op X0 X1) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e3554 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3554
          have b5e3610 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op X0 X1) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3589 X0 X1
               have i₂ := b5e13 (σ x) (σ x) X0 X1
               grind)
            | exact superpose b5e13 b5e3589
            | (have j0 := b5e3589 X0 X1
               grind)
            | exact resolve b5e3589 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3589
          have b5e3624 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (M.op X0 X1) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e3610 X0 X1
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e3610
            | (have j0 := b5e3610 X0 X1
               grind)
            | exact resolve b5e3610 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3610
          have b5e3629 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e3624 X0 X1
               grind)
            | (have r₁ := b5e3624 X0 X1
               have r₂ := b5e538
               grind)
            | exact resolve b5e3624 b5e538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3624
          have b5e5456 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e3629 (M.op x x) (σ x)
               have i₂ := b5e3629 x x
               grind)
            | exact superpose b5e3629 b5e3629
            | exact resolve b5e3629 b5e3629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3629
          have b5e5500 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e5456
          have b5e5502 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e5500
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e5500
            | exact resolve b5e5500 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e5500
          have b5e5503 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e5502
               have r₂ := b5e538
               grind)
            | exact resolve b5e5502 b5e538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e538 b5e5502
          have b5e5603 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (σ x) (σ y)
               have i₂ := b5e5503
               grind)
            | exact superpose b5e5503 b5e13
            | exact resolve b5e13 b5e5503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5735 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e5603 X0 (σ y)
               have i₂ := b5e5503
               grind)
            | exact superpose b5e5503 b5e5603
            | exact resolve b5e5603 b5e5503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5503 b5e5603
          have b5e6266 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e5735 (σ x)
               grind)
            | exact superpose b5e5735 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e5735 (σ x)
               grind)
            | exact resolve b5e24 b5e5735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5735
          have b5e6292 : False := by grind
          exact b5e6292
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e61 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e65 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e61
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e23
               grind)
            | exact resolve b7e65 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
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
          have b7e71 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : x = (k x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e71
            | exact resolve b7e71 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e84 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
          have b7e100 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e22
               grind)
            | exact resolve b7e84 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e103 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e100
               have r₂ := b7e21
               grind)
            | exact resolve b7e100 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e105 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
          have b7e106 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e105
               have r₂ := b7e22
               grind)
            | exact resolve b7e105 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e108 : x = (M.op x y) := by
            first
            | (have r₁ := b7e106
               have r₂ := b7e21
               grind)
            | exact resolve b7e106 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e120 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 x y
               have i₂ := b7e108
               grind)
            | exact superpose b7e108 b7e13
            | exact resolve b7e13 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e144 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b7e31 (M.op x y)
               have i₂ := b7e103
               grind)
            | exact superpose b7e103 b7e31
            | exact resolve b7e31 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e103
          have b7e151 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b7e144
               have i₂ := b7e120 (M.op x y) y
               grind)
            | exact superpose b7e120 b7e144
            | exact resolve b7e144 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120 b7e144
          have b7e152 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e151
               have i₂ := b7e108
               grind)
            | exact superpose b7e108 b7e151
            | exact resolve b7e151 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108 b7e151
          have b7e153 : False := by grind
          exact b7e153
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e80 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e80
            | (have j0 := b8e80 X0 X1
               grind)
            | exact resolve b8e80 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e96 x y
               grind)
            | exact superpose b8e96 b8e20
            | (have j1 := b8e96 x y
               grind)
            | exact resolve b8e20 b8e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e96
          have b8e554 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e500
               have r₂ := b8e23
               grind)
            | exact resolve b8e500 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e500
          have b8e1868 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e554
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e554
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e554
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e554
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e554 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e554
          have b8e1869 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
          clear b8e1868
          have b8e1873 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have r₁ := b8e1869
               have r₂ := b8e22
               grind)
            | exact resolve b8e1869 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1869
          have b8e1877 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1873
               have r₂ := b8e21
               grind)
            | exact resolve b8e1873 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1873
          have b8e1881 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e1877
               grind)
            | exact superpose b8e1877 b8e24
            | exact resolve b8e24 b8e1877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1877
          have b8e1902 : False := by grind
          exact b8e1902

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_y_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
      have b0e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e60 (σ X0)
           grind)
        | exact superpose b0e60 b0e17
        | exact resolve b0e17 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e71 X0
           have i₂ := b0e60 X0
           grind)
        | exact superpose b0e60 b0e71
        | exact resolve b0e71 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60 b0e71
      have b0e256 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e72 x
           grind)
        | exact superpose b0e72 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e72 x
           grind)
        | exact resolve b0e22 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e72
      have b0e267 : False := by grind
      exact b0e267
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
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
        have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b1e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e28 X0 X1 x X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e28
          | exact resolve b1e28 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e59 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : (k x y) = (M.op y y) := by grind
        clear b1e60
        have b1e66 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e59
        have b1e68 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e66
          | exact resolve b1e66 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e72 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e68
          | exact resolve b1e68 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e64 (σ X0)
             grind)
          | exact superpose b1e64 b1e18
          | exact resolve b1e18 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e75 X0
             have i₂ := b1e64 X0
             grind)
          | exact superpose b1e64 b1e75
          | exact resolve b1e75 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e75
        have b1e84 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
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
        have b1e86 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e84 X0
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e84
          | (have j0 := b1e84 X0
             grind)
          | exact resolve b1e84 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e211 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e23
          | exact resolve b1e23 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e641 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e86 (σ x)
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e86
          | (have j0 := b1e86 (σ x)
             grind)
          | (have r₁ := b1e86 (σ x)
             have r₂ := b1e72
             grind)
          | exact resolve b1e86 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e86
        have b1e642 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e641
        have b1e643 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e642
             have i₂ := b1e76 x
             grind)
          | exact superpose b1e76 b1e642
          | exact resolve b1e642 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e642
        have b1e644 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e643
             have r₂ := b1e211
             grind)
          | exact resolve b1e643 b1e211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e643
        have b1e645 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e644
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e644
          | exact resolve b1e644 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e644
        have b1e646 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e645
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e645
          | exact resolve b1e645 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e645
        have b1e648 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e211
             have i₂ := b1e646
             grind)
          | exact superpose b1e646 b1e211
          | exact resolve b1e211 b1e646
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e211
        have b1e654 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e646
             grind)
          | exact superpose b1e646 b1e13
          | exact resolve b1e13 b1e646
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e646
        have b1e655 : y = (M.op y y) := by
          first
          | (have i₁ := b1e654
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e654
          | exact resolve b1e654 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e654
        have b1e780 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e29 y y x
             have i₂ := b1e655
             grind)
          | exact superpose b1e655 b1e29
          | exact resolve b1e29 b1e655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e655
        have b1e898 : y = (M.op x x) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e780 x
             grind)
          | exact superpose b1e780 b1e20
          | exact resolve b1e20 b1e780
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e780
        have b1e1645 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e648
             have i₂ := b1e898
             grind)
          | exact superpose b1e898 b1e648
          | exact resolve b1e648 b1e898
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e648 b1e898
        have b1e1646 : False := by grind
        exact b1e1646
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e54 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : (k x y) = (M.op y y) := by grind
        clear b2e54
        have b2e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e59 (σ X0)
             grind)
          | exact superpose b2e59 b2e18
          | exact resolve b2e18 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e67 X0
             have i₂ := b2e59 X0
             grind)
          | exact superpose b2e59 b2e67
          | exact resolve b2e67 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e67
        have b2e131 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e233 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e68 y
             grind)
          | exact superpose b2e68 b2e22
          | exact resolve b2e22 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e531 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e131 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131
        have b2e532 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e531
             have r₂ := b2e21
             grind)
          | exact resolve b2e531 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e531
        have b2e533 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e532
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e532
          | exact resolve b2e532 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e532
        have b2e534 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e533
             have i₂ := b2e60
             grind)
          | exact superpose b2e60 b2e533
          | exact resolve b2e533 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60 b2e533
        have b2e535 : False := by grind
        exact b2e535
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b3e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b3e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e32 X0 X1 x X3
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e32
          | exact resolve b3e32 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X2 (M.op X0 X1)
             have i₂ := b3e33 X0 X1 X2
             grind)
          | exact superpose b3e33 b3e15
          | (have j0 := b3e15 X2 (M.op X0 X1)
             grind)
          | (have r₁ := b3e15 X1 (M.op X1 X1)
             have r₂ := b3e33 X1 X1 X1
             grind)
          | exact resolve b3e15 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e61 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e61
        have b3e71 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e68
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e68
          | exact resolve b3e68 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e72 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) ≠ (M.op X2 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e60 X0 X1 X2
             have i₂ := b3e33 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b3e33 b3e60
          | (have j0 := b3e60 X0 X1 X2
             grind)
          | (have r₁ := b3e60 X0 X1 (M.op X0 X1)
             have r₂ := b3e33 X0 X1 (M.op X0 X1)
             grind)
          | (have r₁ := b3e60 x (M.op X1 X1) X1
             have r₂ := b3e33 X1 X1 x
             grind)
          | exact resolve b3e60 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e66 (σ X0)
             grind)
          | exact superpose b3e66 b3e18
          | exact resolve b3e18 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e77 X0
             have i₂ := b3e66 X0
             grind)
          | exact superpose b3e66 b3e77
          | exact resolve b3e77 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e84 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 x (M.op X0 X1)
             have i₂ := b3e33 X0 X1 x
             grind)
          | exact superpose b3e33 b3e16
          | (have j0 := b3e16 X2 (M.op X0 X1)
             grind)
          | exact resolve b3e16 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e88 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ y = (k X0 y) := by
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
        have b3e92 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e84 X0 X1 X2
             have j1 := b3e72 X0 X1 X2
             grind)
          | (have r₁ := b3e84 X0 X1 X2
             have r₂ := b3e72 X0 X1 X2
             grind)
          | (have r₁ := b3e84 X2 X2 X1
             have r₂ := b3e72 X1 X1 X2
             grind)
          | exact resolve b3e84 b3e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72 b3e84
        have b3e96 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e92 X0 X1 X2
             grind)
          | (have r₁ := b3e92 X0 X1 X2
             have r₂ := b3e33 X0 X1 (M.op X0 X1)
             grind)
          | exact resolve b3e92 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
        have b3e166 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e157 X0 X1
             have i₂ := b3e80 X0
             grind)
          | exact superpose b3e80 b3e157
          | (have j0 := b3e157 X0 X1
             grind)
          | exact resolve b3e157 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157
        have b3e177 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e166 X0 X1
             have i₂ := b3e80 X1
             grind)
          | exact superpose b3e80 b3e166
          | (have j0 := b3e166 X0 X1
             grind)
          | exact resolve b3e166 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e166
        have b3e202 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e71
             grind)
          | exact superpose b3e71 b3e15
          | exact resolve b3e15 b3e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e203 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e33 (σ y) (σ y) x
             have i₂ := b3e71
             grind)
          | exact superpose b3e71 b3e33
          | exact resolve b3e33 b3e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e71
        have b3e206 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e202
        have b3e207 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e206
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e206
          | exact resolve b3e206 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e206
        have b3e209 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e207
             have i₂ := b3e66 y
             grind)
          | exact superpose b3e66 b3e207
          | exact resolve b3e207 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66 b3e207
        have b3e210 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e209
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e209
          | exact resolve b3e209 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209
        have b3e213 : (k x y) = (τ (σ (M.op x y))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e210
             grind)
          | exact superpose b3e210 b3e13
          | exact resolve b3e13 b3e210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e214 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b3e213
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e213
          | exact resolve b3e213 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e213
        have b3e255 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by
          first
          | (have j0 := b3e88 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e256 : y = (k x y) := by
          first
          | (have r₁ := b3e255
             have r₂ := b3e20
             grind)
          | exact resolve b3e255 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e255
        have b3e259 : y = (M.op x y) := by
          first
          | (have i₁ := b3e214
             have i₂ := b3e256
             grind)
          | exact superpose b3e256 b3e214
          | exact resolve b3e214 b3e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e214
        have b3e260 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e210
             have i₂ := b3e256
             grind)
          | exact superpose b3e256 b3e210
          | exact resolve b3e210 b3e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e256
        have b3e327 : ∀ X0 : G, y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e96 x y x
             have i₂ := b3e259
             grind)
          | exact superpose b3e259 b3e96
          | exact resolve b3e96 b3e259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96 b3e259
        have b3e876 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e177 x y
             grind)
          | exact superpose b3e177 b3e22
          | (have j1 := b3e177 x y
             grind)
          | exact resolve b3e22 b3e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e177
        have b3e944 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e876
             have i₂ := b3e210
             grind)
          | exact superpose b3e210 b3e876
          | exact resolve b3e876 b3e210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210 b3e876
        have b3e1027 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b3e944
             have r₂ := b3e23
             grind)
          | exact resolve b3e944 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e944
        have b3e1075 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e1027
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1027
          | exact resolve b3e1027 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1027
        have b3e1102 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e1075
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1075
          | exact resolve b3e1075 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1075
        have b3e1119 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b3e1102
             have r₂ := b3e23
             grind)
          | exact resolve b3e1102 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1102
        have b3e1149 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e80 x
             grind)
          | exact superpose b3e80 b3e23
          | exact resolve b3e23 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e80
        have b3e1177 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e1149
             have i₂ := b3e260
             grind)
          | exact superpose b3e260 b3e1149
          | exact resolve b3e1149 b3e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e260 b3e1149
        have b3e2828 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e203 X0
             have i₂ := b3e327 x
             grind)
          | exact superpose b3e327 b3e203
          | exact resolve b3e203 b3e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203 b3e327
        have b3e3133 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e1119
             have i₂ := b3e2828 (σ x)
             grind)
          | exact superpose b3e2828 b3e1119
          | exact resolve b3e1119 b3e2828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1119 b3e2828
        have b3e3206 : False := by grind
        exact b3e3206
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e69 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e69
          have b4e80 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e77
            | exact resolve b4e77 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e84 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e80
               have i₂ := b4e75 y
               grind)
            | exact superpose b4e75 b4e80
            | exact resolve b4e80 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e80
          have b4e86 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e84
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e84
            | exact resolve b4e84 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84
          have b4e87 : False := by grind
          exact b4e87
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
            | (have i₁ := b5e33 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
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
          clear b5e34
          have b5e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e70 (σ X0)
               grind)
            | exact superpose b5e70 b5e19
            | exact resolve b5e19 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e79
            | exact resolve b5e79 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e79
          have b5e91 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ y = (k X0 y) := by
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
          have b5e160 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e231 : (M.op x y) = (M.op x x) ∨ y = (k x y) := by
            first
            | (have j0 := b5e91 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e232 : y = (k x y) := by
            first
            | (have r₁ := b5e231
               have r₂ := b5e21
               grind)
            | exact resolve b5e231 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e231
          have b5e563 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e160 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e160
          have b5e564 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e563
               have r₂ := b5e23
               grind)
            | exact resolve b5e563 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e563
          have b5e565 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e564
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e564
            | exact resolve b5e564 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e564
          have b5e566 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e565
               have i₂ := b5e232
               grind)
            | exact superpose b5e232 b5e565
            | exact resolve b5e565 b5e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e232 b5e565
          have b5e570 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e566
               grind)
            | exact superpose b5e566 b5e20
            | exact resolve b5e20 b5e566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e575 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e40 (σ x) (σ y)
               have i₂ := b5e566
               grind)
            | exact superpose b5e566 b5e40
            | exact resolve b5e40 b5e566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e566
          have b5e579 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e575
               have i₂ := b5e84 y
               grind)
            | exact superpose b5e84 b5e575
            | exact resolve b5e575 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e575
          have b5e584 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b5e579
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e579
            | exact resolve b5e579 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e579
          have b5e587 : False := by grind
          exact b5e587
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e58 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e58
        have b6e64 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e62
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e62
          | exact resolve b6e62 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e193 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e15
          | exact resolve b6e15 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e197 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e193
        have b6e198 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e197
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e197
          | exact resolve b6e197 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e197
        have b6e200 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e198
             have i₂ := b6e61 y
             grind)
          | exact superpose b6e61 b6e198
          | exact resolve b6e198 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e198
        have b6e204 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e200
             grind)
          | exact superpose b6e200 b6e13
          | exact resolve b6e13 b6e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e200
        have b6e205 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e204
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e204
          | exact resolve b6e204 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204
        have b6e221 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e205
             grind)
          | exact superpose b6e205 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e205
        have b6e222 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e221
        have b6e224 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e222
             have r₂ := b6e21
             grind)
          | exact resolve b6e222 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e222
        have b6e226 : False := by grind
        exact b6e226
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b7e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e32 X0 X1 x X3
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e32
            | exact resolve b7e32 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
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
          have b7e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e66
          have b7e73 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e71
            | exact resolve b7e71 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e77 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e70 y
               grind)
            | exact superpose b7e70 b7e73
            | exact resolve b7e73 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e70 (σ X0)
               grind)
            | exact superpose b7e70 b7e19
            | exact resolve b7e19 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e80 X0
               have i₂ := b7e70 X0
               grind)
            | exact superpose b7e70 b7e80
            | exact resolve b7e80 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e80
          have b7e94 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
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
          have b7e96 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e94 X0
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e94
            | (have j0 := b7e94 X0
               grind)
            | exact resolve b7e94 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e196 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e23
            | exact resolve b7e23 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e205 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e196
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e196
            | exact resolve b7e196 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e196
          have b7e470 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e96 (σ x)
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e96
            | (have j0 := b7e96 (σ x)
               grind)
            | (have r₁ := b7e96 (σ x)
               have r₂ := b7e77
               grind)
            | exact resolve b7e96 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e96
          have b7e473 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e470
          have b7e474 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e473
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e473
            | exact resolve b7e473 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e473
          have b7e475 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e474
               have r₂ := b7e205
               grind)
            | exact resolve b7e474 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e205 b7e474
          have b7e476 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e475
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e475
            | exact resolve b7e475 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e475
          have b7e485 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e476
               grind)
            | exact superpose b7e476 b7e14
            | exact resolve b7e14 b7e476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e476
          have b7e486 : y = (k x y) := by
            first
            | (have i₁ := b7e485
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e485
            | exact resolve b7e485 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e485
          have b7e561 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e486
               grind)
            | exact superpose b7e486 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e486
          have b7e562 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e561
               have r₂ := b7e21
               grind)
            | exact resolve b7e561 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e561
          have b7e568 : y = (M.op x y) := by
            first
            | (have r₁ := b7e562
               have r₂ := b7e22
               grind)
            | exact resolve b7e562 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e562
          have b7e634 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e33 x y x
               have i₂ := b7e568
               grind)
            | exact superpose b7e568 b7e33
            | exact resolve b7e33 b7e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e770 : y ≠ (M.op x y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e634 y
               grind)
            | exact superpose b7e634 b7e22
            | exact resolve b7e22 b7e634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e634
          have b7e798 : False := by grind
          exact b7e798
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e151 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e456 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e151 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151
          have b8e457 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e456
               have r₂ := b8e23
               grind)
            | exact resolve b8e456 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e456
          have b8e458 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e457
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e457
            | exact resolve b8e457 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e457
          have b8e463 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e458
               grind)
            | exact superpose b8e458 b8e20
            | exact resolve b8e20 b8e458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e458
          have b8e514 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e463
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e463
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e463 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463
          have b8e515 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e514
          have b8e517 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e515
               have r₂ := b8e21
               grind)
            | exact resolve b8e515 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e515
          have b8e520 : False := by grind
          exact b8e520

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
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
        have b1e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e52 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e53 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e52
             have r₂ := b1e23
             grind)
          | exact resolve b1e52 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e54 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e54
          | exact resolve b1e54 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e54
        have b1e56 : False := by grind
        exact b1e56
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
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e187 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e825 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e187 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e187
          | (have j0 := b2e187 x y
             grind)
          | exact resolve b2e187 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e187
        have b2e832 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e825
        have b2e840 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e832
             have r₂ := b2e22
             grind)
          | exact resolve b2e832 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e832
        have b2e847 : False := by grind
        exact b2e847
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
        have b3e46 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e48 : x = y ∨ x = (k x y) := by grind
        clear b3e46
        have b3e49 : x = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e23
             grind)
          | exact resolve b3e48 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e48
        have b3e52 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e29
          | exact resolve b3e29 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e49
        have b3e53 : False := by grind
        exact b3e53
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
               have i₂ := b5e28 X0 X1
               grind)
            | exact superpose b5e28 b5e14
            | exact resolve b5e14 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e34 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
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
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b5e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e36 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e36
            | exact resolve b5e36 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e42 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op y y) X1
               have i₂ := b5e34 (M.op X0 (M.op y y))
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b5e42 x X1
               have i₂ := b5e34 x
               grind)
            | exact superpose b5e34 b5e42
            | exact resolve b5e42 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e47 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = X0 ∨ (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 (M.op y y)
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e17
            | (have j0 := b5e17 y y
               grind)
            | exact resolve b5e17 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e49 : ∀ X0 : G, y = X0 ∨ (k X0 (M.op y y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e47 X0
               grind)
            | (have r₁ := b5e47 X0
               have r₂ := b5e43 y
               grind)
            | exact resolve b5e47 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e51 : ∀ X0 : G, (k X0 y) = X0 ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b5e49 X0
               have i₂ := b5e43 y
               grind)
            | exact superpose b5e43 b5e49
            | (have j0 := b5e49 X0
               grind)
            | exact resolve b5e49 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e49
          have b5e73 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e38 (M.op X0 X1) X1 x
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e152 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 (M.op X0 X1) X1
               have i₂ := b5e73 X0 X1
               grind)
            | exact superpose b5e73 b5e16
            | (have j0 := b5e16 (M.op X0 X1) X1
               grind)
            | (have r₁ := b5e16 (M.op X0 X1) X1
               have r₂ := b5e73 X0 X1
               grind)
            | exact resolve b5e16 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e160 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e152 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e152
          have b5e207 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 (M.op X1 (σ X0)) X0
               have i₂ := b5e160 X1 (σ X0)
               grind)
            | exact superpose b5e160 b5e33
            | exact resolve b5e33 b5e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e160
          have b5e213 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e207 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e207
            | exact resolve b5e207 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e207
          have b5e317 : ∀ X0 : G, y = (τ (M.op X0 (σ y))) ∨ y = (τ (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e51 (τ (M.op X0 (σ y)))
               have i₂ := b5e213 y X0
               grind)
            | exact superpose b5e213 b5e51
            | (have j0 := b5e51 (τ (M.op X0 (σ y)))
               grind)
            | exact resolve b5e51 b5e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e213
          have b5e318 : ∀ X0 : G, y = (τ (M.op X0 (σ y))) := by
            intro X0
            first
            | (have j0 := b5e317 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e317
          have b5e363 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e15 (M.op X0 (σ y))
               have i₂ := b5e318 X0
               grind)
            | exact superpose b5e318 b5e15
            | exact resolve b5e15 b5e318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e318
          have b5e395 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e363 (σ x)
               grind)
            | exact superpose b5e363 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e363 (σ x)
               grind)
            | exact resolve b5e24 b5e363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e363
          have b5e397 : False := by grind
          exact b5e397
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
        have b6e53 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e55 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e53
        have b6e58 : x = (M.op x y) := by
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
          have b7e46 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e25
               grind)
            | exact resolve b7e50 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e50
          have b7e54 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e52
            | exact resolve b7e52 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e57 : (k x y) = (τ (σ x)) := by
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
          have b7e58 : x = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e67 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e68 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e67
          have b7e70 : y = (M.op x y) := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e21
               grind)
            | exact resolve b7e68 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e72 : False := by grind
          exact b7e72
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
          have b8e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e110 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e59 x y
               grind)
            | exact superpose b8e59 b8e20
            | (have j1 := b8e59 x y
               grind)
            | exact resolve b8e20 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e124 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e110
               have r₂ := b8e24
               grind)
            | exact resolve b8e110 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e127 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e124
               have r₂ := b8e23
               grind)
            | exact resolve b8e124 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e128 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e127
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e127
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e127 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e129 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e128
          have b8e130 : x = (M.op x y) := by
            first
            | (have r₁ := b8e129
               have r₂ := b8e22
               grind)
            | exact resolve b8e129 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e131 : False := by grind
          exact b8e131

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_y_x_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
        have b1e25 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) (σ y)
             grind)
          | (have r₁ := b1e15 (σ y) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e25
        have b1e28 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e26
          | exact resolve b1e26 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e33 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e13
          | exact resolve b1e13 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e34 : y = (k y y) := by
          first
          | (have i₁ := b1e33
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e33
          | exact resolve b1e33 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e38 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b1e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e40 X0 X1 x X3
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e40
          | exact resolve b1e40 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e44 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e38 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e38
          | exact resolve b1e38 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e65 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e34
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e34
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e34 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e74 : y = (M.op y y) := by grind
        clear b1e65
        have b1e91 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e44 (σ x)
             grind)
          | exact superpose b1e44 b1e21
          | exact resolve b1e21 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e103 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e42 y y x
             have i₂ := b1e74
             grind)
          | exact superpose b1e74 b1e42
          | exact resolve b1e42 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e74
        have b1e120 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e103 x
             grind)
          | exact superpose b1e103 b1e20
          | exact resolve b1e20 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103
        have b1e129 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e91
             have i₂ := b1e120
             grind)
          | exact superpose b1e120 b1e91
          | exact resolve b1e91 b1e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91 b1e120
        have b1e134 : False := by grind
        exact b1e134
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
        have b2e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e26 X0 X1
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e12 x y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
        have b2e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e34 X0 X1 x X3
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e38 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e32 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e32
          | exact resolve b2e32 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e45 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 x
             have i₂ := b2e38 x
             grind)
          | exact superpose b2e38 b2e16
          | (have j0 := b2e16 X0 x
             grind)
          | (have r₁ := b2e16 X0 x
             have r₂ := b2e38 x
             grind)
          | exact resolve b2e16 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b2e45 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e47 : ∀ X0 : G, (k X0 x) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b2e46 X0
             have i₂ := b2e38 X0
             grind)
          | exact superpose b2e38 b2e46
          | (have j0 := b2e46 X0
             grind)
          | exact resolve b2e46 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e46
        have b2e60 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
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
        have b2e61 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e60 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e79 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e36 (M.op X0 X1) X1 x
             grind)
          | exact superpose b2e36 b2e12
          | exact resolve b2e12 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e80 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = X2 ∨ (k X2 (M.op X0 X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 X2 (M.op X0 X1)
             have i₂ := b2e36 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e36 b2e16
          | (have j0 := b2e16 X2 (M.op X0 X1)
             grind)
          | (have r₁ := b2e16 X0 (M.op X0 X1)
             have r₂ := b2e36 X0 X1 (M.op X0 X1)
             grind)
          | exact resolve b2e16 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e84 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = X2 ∨ (k X2 (M.op X0 X1)) = X2 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e80 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e87 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = X2 ∨ (M.op X0 X1) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e84 X0 X1 X2
             have i₂ := b2e36 X0 X1 X2
             grind)
          | exact superpose b2e36 b2e84
          | (have j0 := b2e84 X0 X1 X2
             grind)
          | exact resolve b2e84 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e84
        have b2e115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (M.op X0 X1) X1
             have i₂ := b2e79 X0 X1
             grind)
          | exact superpose b2e79 b2e15
          | (have j0 := b2e15 (M.op X0 X1) X1
             grind)
          | (have r₁ := b2e15 (M.op X0 X1) X1
             have r₂ := b2e79 X0 X1
             grind)
          | exact resolve b2e15 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e119 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e115 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115
        have b2e122 : ∀ X0 : G, (k X0 (σ (σ y))) = (σ (M.op (τ X0) (σ y))) ∨ (τ X0) = (M.op (τ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 (σ y)
             have i₂ := b2e61 (τ X0)
             grind)
          | exact superpose b2e61 b2e26
          | (have j1 := b2e61 (τ X0)
             grind)
          | exact resolve b2e26 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e385 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e31 (M.op X1 (σ X0)) X0
             have i₂ := b2e119 X1 (σ X0)
             grind)
          | exact superpose b2e119 b2e31
          | exact resolve b2e31 b2e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e119
        have b2e395 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e385 X0 X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e385
          | exact resolve b2e385 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e385
        have b2e483 : ∀ X0 : G, x = (τ (M.op X0 (σ x))) ∨ x = (τ (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e47 (τ (M.op X0 (σ x)))
             have i₂ := b2e395 x X0
             grind)
          | exact superpose b2e395 b2e47
          | (have j0 := b2e47 (τ (M.op X0 (σ x)))
             grind)
          | exact resolve b2e47 b2e395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e484 : ∀ X0 : G, x = (τ (M.op X0 (σ x))) := by
          intro X0
          first
          | (have j0 := b2e483 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e483
        have b2e535 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e14 (M.op X0 (σ x))
             have i₂ := b2e484 X0
             grind)
          | exact superpose b2e484 b2e14
          | exact resolve b2e14 b2e484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e484
        have b2e599 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e87 X0 (σ x) x
             have i₂ := b2e535 X0
             grind)
          | exact superpose b2e535 b2e87
          | exact resolve b2e87 b2e535
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87 b2e535
        have b2e1430 : ∀ X0 : G, (σ x) = (τ (M.op X0 (σ (σ x)))) ∨ (σ x) = (τ (M.op X0 (σ (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e395 (σ x) X0
             have i₂ := b2e599 (τ (M.op X0 (σ (σ x))))
             grind)
          | exact superpose b2e599 b2e395
          | (have j1 := b2e599 (τ (M.op X0 (σ (σ x))))
             grind)
          | exact resolve b2e395 b2e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e395 b2e599
        have b2e1433 : ∀ X0 : G, (σ x) = (τ (M.op X0 (σ (σ x)))) := by
          intro X0
          first
          | (have j0 := b2e1430 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1430
        have b2e1601 : ∀ X0 X1 : G, (k (M.op X0 (σ (σ x))) (σ X1)) = (σ (k (σ x) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e26 (M.op X0 (σ (σ x))) X1
             have i₂ := b2e1433 X0
             grind)
          | exact superpose b2e1433 b2e26
          | exact resolve b2e26 b2e1433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e1603 : ∀ X0 : G, (k (M.op X0 (σ (σ x))) (σ (σ y))) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e122 (M.op X0 (σ (σ x)))
             have i₂ := b2e1433 X0
             grind)
          | exact superpose b2e1433 b2e122
          | exact resolve b2e122 b2e1433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122 b2e1433
        have b2e1609 : ∀ X0 : G, (k (M.op X0 (σ (σ x))) (σ (σ y))) = (σ (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have j0 := b2e1603 X0
             grind)
          | (have r₁ := b2e1603 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e1603 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1603
        have b2e1612 : (σ (M.op (σ x) (σ y))) = (σ (k (σ x) (σ y))) := by
          first
          | (have i₁ := b2e1609 x
             have i₂ := b2e1601 x (σ y)
             grind)
          | exact superpose b2e1601 b2e1609
          | exact resolve b2e1609 b2e1601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1601 b2e1609
        have b2e1614 : (σ (M.op (σ x) (σ y))) = (σ (σ (k x y))) := by
          first
          | (have i₁ := b2e1612
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1612
          | exact resolve b2e1612 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1612
        have b2e1616 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b2e1614
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1614
          | exact resolve b2e1614 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1614
        have b2e2251 : (M.op (σ x) (σ y)) = (τ (σ (σ y))) := by
          first
          | (have i₁ := b2e13 (M.op (σ x) (σ y))
             have i₂ := b2e1616
             grind)
          | exact superpose b2e1616 b2e13
          | exact resolve b2e13 b2e1616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1616
        have b2e2283 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e2251
             have i₂ := b2e13 (σ y)
             grind)
          | exact superpose b2e13 b2e2251
          | exact resolve b2e2251 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2251
        have b2e2462 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e79 (σ x) (σ y)
             have i₂ := b2e2283
             grind)
          | exact superpose b2e2283 b2e79
          | exact resolve b2e79 b2e2283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79 b2e2283
        have b2e2467 : False := by grind
        exact b2e2467
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e25
        have b3e28 : (σ y) = (σ (k x y)) := by
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
        have b3e31 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b3e12 y y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e31
          | exact resolve b3e31 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e41 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e39 x
             grind)
          | exact superpose b3e39 b3e20
          | exact resolve b3e20 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e39 y
             grind)
          | exact superpose b3e39 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e39 y
             grind)
          | exact resolve b3e16 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e49 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e52 : ∀ X0 : G, (k X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e50 X0
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e50
          | (have j0 := b3e50 X0
             grind)
          | exact resolve b3e50 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e50
        have b3e76 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e77 : y = (k x y) := by
          first
          | (have i₁ := b3e76
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e76
          | exact resolve b3e76 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e111 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e52 x
             grind)
          | exact superpose b3e52 b3e77
          | (have j1 := b3e52 x
             grind)
          | exact resolve b3e77 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e77
        have b3e113 : x = y := by grind
        clear b3e111
        have b3e118 : False := by grind
        exact b3e118
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e13 y y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e44 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e81 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e43 (σ x)
               grind)
            | exact superpose b4e43 b4e20
            | exact resolve b4e20 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e91 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e81
               have i₂ := b4e44 x
               grind)
            | exact superpose b4e44 b4e81
            | exact resolve b4e81 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e81
          have b4e92 : False := by grind
          exact b4e92
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b5e33 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b5e13 y y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b5e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e35 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e39 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e33 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e64 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
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
          have b5e65 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e64 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e82 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e37 (M.op X0 X1) X1 x
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e16 (M.op X0 X1) X1
               have i₂ := b5e82 X0 X1
               grind)
            | exact superpose b5e82 b5e16
            | (have j0 := b5e16 (M.op X0 X1) X1
               grind)
            | (have r₁ := b5e16 (M.op X0 X1) X1
               have r₂ := b5e82 X0 X1
               grind)
            | exact resolve b5e16 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e122 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e118 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e137 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e28 X0 (M.op X1 (τ X0))
               have i₂ := b5e122 X1 (τ X0)
               grind)
            | exact superpose b5e122 b5e28
            | exact resolve b5e28 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e122
          have b5e141 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e137 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e137
            | exact resolve b5e137 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137
          have b5e185 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 (τ (σ y)))) (σ y)) ∨ (σ (M.op X0 (τ (σ y)))) = (M.op (σ (M.op X0 (τ (σ y)))) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e65 (σ (M.op X0 (τ (σ y))))
               have i₂ := b5e141 (σ y) X0
               grind)
            | exact superpose b5e141 b5e65
            | (have j0 := b5e65 (σ (M.op X0 (τ (σ y))))
               grind)
            | exact resolve b5e65 b5e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e141
          have b5e191 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 y)) (σ y)) ∨ (σ (M.op X0 (τ (σ y)))) = (M.op (σ (M.op X0 (τ (σ y)))) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e185 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e185
            | (have j0 := b5e185 X0
               grind)
            | exact resolve b5e185 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185
          have b5e197 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op X0 (τ (σ y)))) = (M.op (σ (M.op X0 (τ (σ y)))) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e191 X0
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e191
            | (have j0 := b5e191 X0
               grind)
            | exact resolve b5e191 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e191
          have b5e199 : ∀ X0 : G, (σ (M.op X0 (τ (σ y)))) = (M.op (σ (M.op X0 (τ (σ y)))) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e197 X0
               grind)
            | (have r₁ := b5e197 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e197 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e197
          have b5e201 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e199 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e199
            | exact resolve b5e199 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e203 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e201 x
               have i₂ := b5e39 x
               grind)
            | exact superpose b5e39 b5e201
            | exact resolve b5e201 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e201
          have b5e205 : False := by grind
          exact b5e205
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
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
        have b6e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 (M.op (M.op X0 X1) X1) X3
             have i₂ := b6e12 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e37 X0 X1 x X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e37
          | exact resolve b6e37 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e56 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e67 : y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e56
             have r₂ := b6e21
             grind)
          | exact resolve b6e56 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e72 : y = (M.op x y) := by
          first
          | (have r₁ := b6e67
             have r₂ := b6e20
             grind)
          | exact resolve b6e67 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e77 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b6e12 x y x
             have i₂ := b6e72
             grind)
          | exact superpose b6e72 b6e12
          | exact resolve b6e12 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e79 : y = (M.op y y) := by
          first
          | (have i₁ := b6e77 x
             have i₂ := b6e39 y y x
             grind)
          | exact superpose b6e39 b6e77
          | exact resolve b6e77 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e77
        have b6e80 : False := by grind
        exact b6e80
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b7e25 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ y)
               grind)
            | (have r₁ := b7e16 (σ y) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b7e25
          have b7e27 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : y = (k y y) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e62 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e71 : y = (M.op y y) := by grind
          clear b7e62
          have b7e76 : False := by grind
          exact b7e76
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
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e279 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 y y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e318 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e279
               have r₂ := b8e24
               grind)
            | exact resolve b8e279 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e279
          have b8e322 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e318
               have r₂ := b8e23
               grind)
            | exact resolve b8e318 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e318
          have b8e326 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e322
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e322
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e322 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322
          have b8e327 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e326
          have b8e330 : x = (M.op x y) := by
            first
            | (have r₁ := b8e327
               have r₂ := b8e22
               grind)
            | exact resolve b8e327 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e327
          have b8e334 : False := by grind
          exact b8e334

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e11 y y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
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
      have b0e37 : ∀ X0 : G, y = (M.op X0 y) := by
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
      have b0e50 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e36 (σ x)
           grind)
        | exact superpose b0e36 b0e18
        | exact resolve b0e18 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e52 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e50
           have i₂ := b0e37 x
           grind)
        | exact superpose b0e37 b0e50
        | exact resolve b0e50 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e50
      have b0e53 : False := by grind
      exact b0e53
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
        have b1e24 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e25 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e28 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e12 y y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e28 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e28
          | exact resolve b1e28 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e37 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e36 x
             grind)
          | exact superpose b1e36 b1e23
          | exact resolve b1e23 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e36
        have b1e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        clear b1e44
        have b1e48 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e48
          | exact resolve b1e48 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e49
          | exact resolve b1e49 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e49
        have b1e51 : False := by grind
        exact b1e51
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e80 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e87 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e80 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e80
          | exact resolve b2e80 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e90 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e17 X0 (σ y)
             have i₂ := b2e87 X0
             grind)
          | exact superpose b2e87 b2e17
          | (have j0 := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e17 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e93 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e90 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e96 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e93 X0
             grind)
          | (have r₁ := b2e93 (σ y)
             have r₂ := b2e21
             grind)
          | (have r₁ := b2e93 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e93 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e115 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e96 (σ x)
             grind)
          | exact superpose b2e96 b2e22
          | (have r₁ := b2e22
             have r₂ := b2e96 (σ x)
             grind)
          | exact resolve b2e22 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e116 : False := by grind
        exact b2e116
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
        have b3e24 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b3e25 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e29 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e25 (σ X0)
             grind)
          | exact superpose b3e25 b3e18
          | exact resolve b3e18 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e31 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e31
          | exact resolve b3e31 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
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
        have b3e48 : y = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e49 : y = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e20
             grind)
          | exact resolve b3e48 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e72 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e37 (σ x)
             grind)
          | exact superpose b3e37 b3e23
          | exact resolve b3e23 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e37
        have b3e96 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29 x
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e29
          | exact resolve b3e29 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e49
        have b3e105 : False := by grind
        exact b3e105
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b5e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e34 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e45 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e48 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e45
          have b5e49 : y = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e266 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36 (σ X0) (σ X1) x
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e36
            | (have j1 := b5e53 X1 X1
               grind)
            | exact resolve b5e36 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e53
          have b5e2602 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e266 x y x
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e266
            | (have j0 := b5e266 y y x
               grind)
            | exact resolve b5e266 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e266
          have b5e2672 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e2602 X0
               grind)
            | (have r₁ := b5e2602 (σ y)
               have r₂ := b5e23
               grind)
            | (have r₁ := b5e2602 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e2602 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2602
          have b5e2687 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e2672 X0
               grind)
            | (have r₁ := b5e2672 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e2672 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2672
          have b5e2698 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e2687 (σ y)
               grind)
            | exact superpose b5e2687 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e2687 (σ y)
               grind)
            | exact resolve b5e23 b5e2687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2687
          have b5e2726 : False := by grind
          exact b5e2726
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
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
        have b6e57 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 X0 y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e63 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e70 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e63 X0
             grind)
          | (have r₁ := b6e63 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e63 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e63 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e77 : x ≠ x := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e70 x
             grind)
          | exact superpose b6e70 b6e21
          | (have r₁ := b6e21
             have r₂ := b6e70 x
             grind)
          | exact resolve b6e21 b6e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e84 : False := by grind
        exact b6e84
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b7e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e30 X0 X1 x X3
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
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
          have b7e70 : (k x y) = (τ (σ y)) := by
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
          have b7e91 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e92 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e21
               grind)
            | exact resolve b7e91 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e94 : y = (M.op x y) := by
            first
            | (have r₁ := b7e92
               have r₂ := b7e22
               grind)
            | exact resolve b7e92 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e105 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e32 x y x
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e32
            | exact resolve b7e32 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e94
          have b7e162 : y ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e105 y
               grind)
            | exact superpose b7e105 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e105 y
               grind)
            | exact resolve b7e21 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e171 : False := by grind
          exact b7e171
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b8e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e173 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e49 x y
               grind)
            | exact superpose b8e49 b8e20
            | (have j1 := b8e49 y y
               grind)
            | exact resolve b8e20 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e206 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e173
               have r₂ := b8e23
               grind)
            | exact resolve b8e173 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e210 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e206
               have r₂ := b8e24
               grind)
            | exact resolve b8e206 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e206
          have b8e229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e210
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e210
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e210 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210
          have b8e230 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e229
          have b8e231 : x = (M.op x y) := by
            first
            | (have r₁ := b8e230
               have r₂ := b8e21
               grind)
            | exact resolve b8e230 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e230
          have b8e232 : False := by grind
          exact b8e232
