import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1171`: `x = y ◇ ((z ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation1171 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1171 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1171.models_iff G M).mp hM
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
      have b0e79 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e85 : False := by grind
      exact b0e85
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
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b4e67 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = X0 ∨ (k X0 y) = (M.op X0 y) := by
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
          have b4e68 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
          have b4e71 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e68 X0
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e68
            | (have j0 := b4e68 X0
               grind)
            | exact resolve b4e68 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e426 : x = y ∨ (M.op x y) = (k x y) := by
            first
            | (have j0 := b4e67 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e428 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e426
               have r₂ := b4e21
               grind)
            | exact resolve b4e426 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e426
          have b4e689 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e71 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e71
            | (have j0 := b4e71 (σ X0)
               grind)
            | (have r₁ := b4e71 (σ x)
               have r₂ := b4e30 x
               grind)
            | exact resolve b4e71 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e71
          have b4e697 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e689 X0
               have i₂ := b4e19 X0 y
               grind)
            | exact superpose b4e19 b4e689
            | (have j0 := b4e689 X0
               grind)
            | exact resolve b4e689 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e689
          have b4e88703 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b4e697 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e697
          have b4e88713 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b4e88703
               have r₂ := b4e23
               grind)
            | exact resolve b4e88703 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88703
          have b4e88749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e88713
               have i₂ := b4e428
               grind)
            | exact superpose b4e428 b4e88713
            | exact resolve b4e88713 b4e428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428 b4e88713
          have b4e88772 : False := by grind
          exact b4e88772
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
          have b5e57 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e59 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e57
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e57
            | exact resolve b5e57 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e60 : False := by grind
          exact b5e60
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
          have b7e59 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e59
            | exact resolve b7e59 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e59
          have b7e73 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e14
            | exact resolve b7e14 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e74 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e73
            | exact resolve b7e73 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e78 : False := by grind
          exact b7e78
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b8e56 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e58 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e56
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e56
            | exact resolve b8e56 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e79 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
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
          have b8e90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e70 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e70
            | (have j0 := b8e70 X0 X1
               grind)
            | exact resolve b8e70 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e90 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e90
            | (have j0 := b8e90 X0 X1
               grind)
            | exact resolve b8e90 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e90
          have b8e279 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e79 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e280 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e279
               have r₂ := b8e21
               grind)
            | exact resolve b8e279 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e279
          have b8e635 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e92 x y
               grind)
            | exact superpose b8e92 b8e20
            | (have j1 := b8e92 y x
               grind)
            | exact resolve b8e20 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e686 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e635
               have r₂ := b8e58
               grind)
            | exact resolve b8e635 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58 b8e635
          have b8e701 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e686
               have r₂ := b8e23
               grind)
            | exact resolve b8e686 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e686
          have b8e712 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e701
               have i₂ := b8e280
               grind)
            | exact superpose b8e280 b8e701
            | exact resolve b8e701 b8e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e280 b8e701
          have b8e713 : False := by grind
          exact b8e713

/-- `Equation1243`: `x = x ◇ (((y ◇ x) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1243 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1243 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1243.models_iff G M).mp hM
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
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e68 : False := by grind
      exact b0e68
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
          have b5e45 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e50 : x = y ∨ x = (k x y) := by grind
          clear b5e45
          have b5e51 : x = (k x y) := by
            first
            | (have r₁ := b5e50
               have r₂ := b5e21
               grind)
            | exact resolve b5e50 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e188 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e1586 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e188 x y
               have i₂ := b5e51
               grind)
            | exact superpose b5e51 b5e188
            | (have j0 := b5e188 x y
               grind)
            | exact resolve b5e188 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e188
          have b5e1593 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e1586
          have b5e1598 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e1593
               have r₂ := b5e24
               grind)
            | exact resolve b5e1593 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1593
          have b5e1602 : False := by grind
          exact b5e1602
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
          have b7e43 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e49 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e59 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e50
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e50 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
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
          have b8e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e50 x y
               grind)
            | exact superpose b8e50 b8e20
            | (have j1 := b8e50 x y
               grind)
            | exact resolve b8e20 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e167 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e156
               have r₂ := b8e24
               grind)
            | exact resolve b8e156 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e173 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e167
               have r₂ := b8e23
               grind)
            | exact resolve b8e167 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167
          have b8e176 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e173
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e173
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e173
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e173
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e173 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e177 : x = (M.op x y) ∨ x = y := by grind
          clear b8e176
          have b8e178 : x = y := by
            first
            | (have r₁ := b8e177
               have r₂ := b8e22
               grind)
            | exact resolve b8e177 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177
          have b8e179 : False := by grind
          exact b8e179

/-- `Equation1253`: `x = x ◇ (((y ◇ y) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation1253 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1253 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1253.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y y) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e28 X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e28
        | exact resolve b0e28 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e27
        | exact resolve b0e27 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e38 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 X0 (M.op y x)
           have i₂ := b0e35 y x
           grind)
        | exact superpose b0e35 b0e35
        | exact resolve b0e35 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e108 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e34 X0 y
           have i₂ := b0e38 (σ y)
           grind)
        | exact superpose b0e38 b0e34
        | exact resolve b0e34 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e132 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e108 (σ x)
           grind)
        | exact superpose b0e108 b0e18
        | exact resolve b0e18 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108
      have b0e137 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e132
           have i₂ := b0e38 x
           grind)
        | exact superpose b0e38 b0e132
        | exact resolve b0e132 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e132
      have b0e138 : False := by grind
      exact b0e138
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e42 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b1e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 X0 (σ x)
             grind)
          | (have r₁ := b1e15 X0 (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e42 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e75 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e49 (σ y)
             grind)
          | exact superpose b1e49 b1e21
          | exact resolve b1e21 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e49 (σ x)
             grind)
          | exact superpose b1e49 b1e22
          | exact resolve b1e22 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e155 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 x
             have i₂ := b1e48 (σ X0)
             grind)
          | exact superpose b1e48 b1e18
          | exact resolve b1e18 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e157 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e155 X0
             have i₂ := b1e49 (σ X0)
             grind)
          | exact superpose b1e49 b1e155
          | exact resolve b1e155 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e155
        have b1e557 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e75
             have i₂ := b1e157 y
             grind)
          | exact superpose b1e157 b1e75
          | exact resolve b1e75 b1e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e558 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e76
             have i₂ := b1e157 x
             grind)
          | exact superpose b1e157 b1e76
          | exact resolve b1e76 b1e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e157
        have b1e652 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e558
             grind)
          | exact superpose b1e558 b1e13
          | exact resolve b1e13 b1e558
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e558
        have b1e654 : x = (k x x) := by
          first
          | (have i₁ := b1e652
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e652
          | exact resolve b1e652 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e652
        have b1e697 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e654
             grind)
          | exact superpose b1e654 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e654
        have b1e698 : x = (M.op x x) := by grind
        clear b1e697
        have b1e855 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 x
             have i₂ := b1e698
             grind)
          | exact superpose b1e698 b1e15
          | (have j0 := b1e15 X0 x
             grind)
          | (have r₁ := b1e15 X0 x
             have r₂ := b1e698
             grind)
          | exact resolve b1e15 b1e698
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e698
        have b1e861 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e855 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e855
        have b1e1504 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e557
             have i₂ := b1e861 y
             grind)
          | exact superpose b1e861 b1e557
          | exact resolve b1e557 b1e861
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e557 b1e861
        have b1e1505 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1504
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1504
          | exact resolve b1e1504 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1504
        have b1e1506 : False := by grind
        exact b1e1506
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e40 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b2e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e68 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e45 (σ y)
             grind)
          | exact superpose b2e45 b2e21
          | exact resolve b2e21 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e83 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e92 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e83 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83
        have b2e98 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e88 X0 X1
             have i₂ := b2e45 (σ X0)
             grind)
          | exact superpose b2e45 b2e88
          | (have j0 := b2e88 X0 X1
             grind)
          | exact resolve b2e88 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88
        have b2e100 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e98 X0 X1
             have i₂ := b2e45 (σ X1)
             grind)
          | exact superpose b2e45 b2e98
          | (have j0 := b2e98 X0 X1
             grind)
          | exact resolve b2e98 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e745 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e92 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e746 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e745 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e745
        have b2e752 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e746 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e746 x
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e746 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e746
        have b2e786 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e23 X0 (τ X0)
             have i₂ := b2e752 (τ X0)
             grind)
          | exact superpose b2e752 b2e23
          | exact resolve b2e23 b2e752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e787 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e786 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e786
          | exact resolve b2e786 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e786
        have b2e795 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b2e787 X0
             have i₂ := b2e45 (τ X0)
             grind)
          | exact superpose b2e45 b2e787
          | exact resolve b2e787 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e787
        have b2e803 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e795 X0
             have i₂ := b2e23 X0 y
             grind)
          | exact superpose b2e23 b2e795
          | exact resolve b2e795 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e795
        have b2e993 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e803 (σ X0)
             grind)
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e803 (σ X0)
             grind)
          | exact superpose b2e803 b2e18
          | exact resolve b2e18 b2e803
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e803
        have b2e1004 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e993 X0
             have i₂ := b2e752 X0
             grind)
          | exact superpose b2e752 b2e993
          | exact resolve b2e993 b2e752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e752 b2e993
        have b2e1029 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1004 X0
             have i₂ := b2e18 X0 y
             grind)
          | exact superpose b2e18 b2e1004
          | exact resolve b2e1004 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1004
        have b2e2654 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e100 y y
             grind)
          | exact superpose b2e100 b2e21
          | (have j1 := b2e100 y y
             grind)
          | exact resolve b2e21 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e2720 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e2654
        have b2e2759 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e2720
             have r₂ := b2e68
             grind)
          | exact resolve b2e2720 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e2720
        have b2e2788 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e2759
             have i₂ := b2e1029 y
             grind)
          | exact superpose b2e1029 b2e2759
          | exact resolve b2e2759 b2e1029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1029 b2e2759
        have b2e2798 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e2788
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2788
          | exact resolve b2e2788 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2788
        have b2e2799 : False := by grind
        exact b2e2799
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e42 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | (have r₁ := b3e15 X0 x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b3e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b3e42 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e75 : (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e49 (σ y)
             grind)
          | exact superpose b3e49 b3e22
          | exact resolve b3e22 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e151 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e48 (σ X0)
             grind)
          | exact superpose b3e48 b3e18
          | exact resolve b3e18 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e153 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e151 X0
             have i₂ := b3e49 (σ X0)
             grind)
          | exact superpose b3e49 b3e151
          | exact resolve b3e151 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e151
        have b3e553 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e75
             have i₂ := b3e153 y
             grind)
          | exact superpose b3e153 b3e75
          | exact resolve b3e75 b3e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75 b3e153
        have b3e604 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e553
             grind)
          | exact superpose b3e553 b3e13
          | exact resolve b3e13 b3e553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e553
        have b3e606 : y = (k y y) := by
          first
          | (have i₁ := b3e604
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e604
          | exact resolve b3e604 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e604
        have b3e752 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e606
             grind)
          | exact superpose b3e606 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e606
        have b3e753 : y = (M.op y y) := by grind
        clear b3e752
        have b3e757 : False := by grind
        exact b3e757
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
          clear b4e25
          have b4e31 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x x) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op (M.op (M.op x x) x) x)
               have i₂ := b4e13 (M.op (M.op X0 X0) X0) x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e31
            | exact resolve b4e31 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e42 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e39 X0 (M.op x x)
               have i₂ := b4e39 x x
               grind)
            | exact superpose b4e39 b4e39
            | exact resolve b4e39 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e48 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e16 X0 (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e49 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e63 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e63 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e81 : (σ y) ≠ (k (σ y) x) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e55 (σ y)
               grind)
            | exact superpose b4e55 b4e23
            | exact resolve b4e23 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e94 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e94 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e562 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e70 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e70 X0
               grind)
            | exact resolve b4e16 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e564 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 X1
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e35
            | (have j1 := b4e70 X0
               grind)
            | exact resolve b4e35 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e583 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e562 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562
          have b4e2735 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e30 X0 x
               have i₂ := b4e54 X0
               grind)
            | exact superpose b4e54 b4e30
            | exact resolve b4e30 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e54
          have b4e15735 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e564 X0 X1
               have i₂ := b4e70 X0
               grind)
            | exact superpose b4e70 b4e564
            | (have j0 := b4e564 X0 X1
               have j1 := b4e70 X0
               grind)
            | exact resolve b4e564 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e564
          have b4e15924 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e15735 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15735
          have b4e16993 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e583 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e583
          have b4e16998 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e16993 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16993
            | (have j0 := b4e16993 X0
               grind)
            | exact resolve b4e16993 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16993
          have b4e17079 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e16998 X0
               have j1 := b4e15924 X0 x
               grind)
            | (have r₁ := b4e16998 X0
               have r₂ := b4e15924 X0 (σ x)
               grind)
            | exact resolve b4e16998 b4e15924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15924 b4e16998
          have b4e17169 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e17079 (σ X0)
               grind)
            | exact superpose b4e17079 b4e19
            | exact resolve b4e19 b4e17079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17079
          have b4e18384 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e17169 y
               grind)
            | exact superpose b4e17169 b4e20
            | exact resolve b4e20 b4e17169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e18386 : ∀ X0 X1 : G, (M.op X1 (σ (k x X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X1 (σ X0)
               have i₂ := b4e17169 X0
               grind)
            | exact superpose b4e17169 b4e38
            | exact resolve b4e38 b4e17169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e17169
          have b4e18946 : ∀ X0 : G, (τ (σ (k x X0))) = (k (τ (σ (k x X0))) x) := by
            intro X0
            first
            | (have i₁ := b4e2735 (σ (k x X0))
               have i₂ := b4e18386 X0 (σ (k x X0))
               grind)
            | exact superpose b4e18386 b4e2735
            | exact resolve b4e2735 b4e18386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2735 b4e18386
          have b4e19069 : ∀ X0 : G, (k x X0) = (k (k x X0) x) := by
            intro X0
            first
            | (have i₁ := b4e18946 X0
               have i₂ := b4e14 (k x X0)
               grind)
            | exact superpose b4e14 b4e18946
            | exact resolve b4e18946 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18946
          have b4e19854 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e18384
               have i₂ := b4e104 x y X0
               grind)
            | exact superpose b4e104 b4e18384
            | (have j1 := b4e104 x y X0
               grind)
            | exact resolve b4e18384 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104 b4e18384
          have b4e19860 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e19854 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19854
          have b4e19863 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e19860 X0
               grind)
            | (have r₁ := b4e19860 X0
               have r₂ := b4e21
               grind)
            | (have r₁ := b4e19860 y
               have r₂ := b4e21
               grind)
            | exact resolve b4e19860 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19860
          have b4e19864 : ∀ X0 : G, (k x X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e19863 X0
               have i₂ := b4e42 X0
               grind)
            | exact superpose b4e42 b4e19863
            | (have j0 := b4e19863 X0
               grind)
            | exact resolve b4e19863 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e19863
          have b4e29623 : (σ y) ≠ (σ y) ∨ (σ y) = (k x (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e19864 (σ y)
               grind)
            | exact superpose b4e19864 b4e23
            | (have j1 := b4e19864 (σ y)
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e19864 (σ y)
               grind)
            | exact resolve b4e23 b4e19864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19864
          have b4e29650 : (σ y) = (k x (σ y)) := by grind
          clear b4e29623
          have b4e30311 : (σ y) = (k (σ y) x) := by
            first
            | (have i₁ := b4e19069 (σ y)
               have i₂ := b4e29650
               grind)
            | exact superpose b4e29650 b4e19069
            | exact resolve b4e19069 b4e29650
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19069 b4e29650
          have b4e30333 : False := by grind
          exact b4e30333
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e46 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e75 : (σ x) ≠ (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e51 (σ x)
               grind)
            | exact superpose b5e51 b5e24
            | exact resolve b5e24 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e89 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b5e99 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e89 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e106 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) x) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e94 X0 X1
               have i₂ := b5e51 (σ X0)
               grind)
            | exact superpose b5e51 b5e94
            | (have j0 := b5e94 X0 X1
               grind)
            | exact resolve b5e94 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) x) ∨ (σ X1) = (k (σ X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e106 X0 X1
               have i₂ := b5e51 (σ X1)
               grind)
            | exact superpose b5e51 b5e106
            | (have j0 := b5e106 X0 X1
               grind)
            | exact resolve b5e106 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106
          have b5e721 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e99 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e722 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e721 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e721
          have b5e728 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e722 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e722 x
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e722 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e722
          have b5e756 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e25 X0 (τ X0)
               have i₂ := b5e728 (τ X0)
               grind)
            | exact superpose b5e728 b5e25
            | exact resolve b5e25 b5e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e757 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e756 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e756
            | exact resolve b5e756 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e756
          have b5e763 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e757 X0
               have i₂ := b5e51 (τ X0)
               grind)
            | exact superpose b5e51 b5e757
            | exact resolve b5e757 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e757
          have b5e769 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e763 X0
               have i₂ := b5e25 X0 x
               grind)
            | exact superpose b5e25 b5e763
            | exact resolve b5e763 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e763
          have b5e949 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e769 (σ X0)
               grind)
            | (have i₁ := b5e19 X0 x
               have i₂ := b5e769 (σ X0)
               grind)
            | exact superpose b5e769 b5e19
            | exact resolve b5e19 b5e769
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e769
          have b5e958 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e949 X0
               have i₂ := b5e728 X0
               grind)
            | exact superpose b5e728 b5e949
            | exact resolve b5e949 b5e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e728 b5e949
          have b5e981 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e958 X0
               have i₂ := b5e19 X0 x
               grind)
            | exact superpose b5e19 b5e958
            | exact resolve b5e958 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e958
          have b5e2557 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) ∨ (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e108 x x
               grind)
            | exact superpose b5e108 b5e24
            | (have j1 := b5e108 x x
               grind)
            | exact resolve b5e24 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e2621 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) := by grind
          clear b5e2557
          have b5e2660 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b5e2621
               have r₂ := b5e75
               grind)
            | exact resolve b5e2621 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75 b5e2621
          have b5e2689 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2660
               have i₂ := b5e981 x
               grind)
            | exact superpose b5e981 b5e2660
            | exact resolve b5e2660 b5e981
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e981 b5e2660
          have b5e2700 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e2689
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2689
            | exact resolve b5e2689 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2689
          have b5e2701 : False := by grind
          exact b5e2701
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (σ y) X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e25 X0 X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e25
          | exact resolve b6e25 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e34 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 X0 (M.op (σ y) x)
             have i₂ := b6e31 (σ y) x
             grind)
          | exact superpose b6e31 b6e31
          | exact resolve b6e31 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b6e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e68 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X0 X2
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X2 X2
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e68 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e45 (σ X0)
             grind)
          | exact superpose b6e45 b6e18
          | exact resolve b6e18 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e378 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e34 (σ y)
             have i₂ := b6e91 y
             grind)
          | exact superpose b6e91 b6e34
          | exact resolve b6e34 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34 b6e91
        have b6e485 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e73 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e486 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e485 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e485
        have b6e490 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e486 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e486 x
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e486 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e486
        have b6e635 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e378
             grind)
          | exact superpose b6e378 b6e13
          | exact resolve b6e13 b6e378
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e378
        have b6e637 : y = (k y y) := by
          first
          | (have i₁ := b6e635
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e635
          | exact resolve b6e635 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e635
        have b6e644 : y = (M.op y y) := by
          first
          | (have i₁ := b6e637
             have i₂ := b6e490 y
             grind)
          | exact superpose b6e490 b6e637
          | exact resolve b6e637 b6e490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e490 b6e637
        have b6e648 : False := by grind
        exact b6e648
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
          have b7e31 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e31 X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e31
            | exact resolve b7e31 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e40 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e37 X0 (M.op (σ x) x)
               have i₂ := b7e37 (σ x) x
               grind)
            | exact superpose b7e37 b7e37
            | exact resolve b7e37 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e46 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e143 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e30 X0 x
               have i₂ := b7e51 X0
               grind)
            | exact superpose b7e51 b7e30
            | exact resolve b7e30 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e51
          have b7e214 : (τ (σ x)) = (k (τ (σ x)) x) := by
            first
            | (have i₁ := b7e143 (σ x)
               have i₂ := b7e40 (σ x)
               grind)
            | exact superpose b7e40 b7e143
            | exact resolve b7e143 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e143
          have b7e222 : x = (k x x) := by
            first
            | (have i₁ := b7e214
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e214
            | exact resolve b7e214 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e214
          have b7e300 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e222
               grind)
            | exact superpose b7e222 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e222
          have b7e301 : x = (M.op x x) := by grind
          clear b7e300
          have b7e303 : False := by grind
          exact b7e303
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e80 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e87 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e80 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e329 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e87 (σ X0)
               grind)
            | exact superpose b8e87 b8e19
            | (have j1 := b8e87 (σ X0)
               grind)
            | exact resolve b8e19 b8e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87
          have b8e16621 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e329 x
               grind)
            | exact superpose b8e329 b8e20
            | (have j1 := b8e329 x
               grind)
            | exact resolve b8e20 b8e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e329
          have b8e16868 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e16621
               have r₂ := b8e24
               grind)
            | exact resolve b8e16621 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16621
          have b8e16986 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e16868
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e16868
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e16868 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16868
          have b8e16999 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e16986
          have b8e17006 : y = (M.op y y) := by
            first
            | (have r₁ := b8e16999
               have r₂ := b8e22
               grind)
            | exact resolve b8e16999 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16999
          have b8e17007 : False := by grind
          exact b8e17007

/-- `Equation1253`: `x = x ◇ (((y ◇ y) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation1253 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1253 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1253.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y y) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e39 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e29
        | exact resolve b0e29 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e42 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e39 X0 (M.op y x)
           have i₂ := b0e39 y x
           grind)
        | exact superpose b0e39 b0e39
        | exact resolve b0e39 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e94 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e38 X0 y
           have i₂ := b0e42 (σ y)
           grind)
        | exact superpose b0e42 b0e38
        | exact resolve b0e38 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e114 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e94 (σ x)
           grind)
        | exact superpose b0e94 b0e18
        | exact resolve b0e18 b0e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e94
      have b0e120 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e114
           have i₂ := b0e42 x
           grind)
        | exact superpose b0e42 b0e114
        | exact resolve b0e114 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e114
      have b0e121 : False := by grind
      exact b0e121
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b1e26 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e79 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 (σ y) X0
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 X0
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ y)
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ y) x
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e164 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e27 X0 y
             have i₂ := b1e26 (τ X0)
             grind)
          | exact superpose b1e26 b1e27
          | exact resolve b1e27 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e27
        have b1e172 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e164 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e164
          | exact resolve b1e164 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e164
        have b1e428 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e172 (σ y)
             have i₂ := b1e85 (σ y)
             grind)
          | exact superpose b1e85 b1e172
          | (have j1 := b1e85 (σ y)
             grind)
          | exact resolve b1e172 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e172
        have b1e433 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e428
        have b1e437 : False := by grind
        exact b1e437
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e72 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ y) X0
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) x
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e72 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e139 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e146 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e139 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e139
          | exact resolve b2e139 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e351 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e146 (σ y)
             have i₂ := b2e77 (σ y)
             grind)
          | exact superpose b2e77 b2e146
          | (have j1 := b2e77 (σ y)
             grind)
          | exact resolve b2e146 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77 b2e146
        have b2e354 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e351
        have b2e358 : False := by grind
        exact b2e358
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e30 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
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
        have b3e37 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x x) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ y) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e38 X0 X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e38
          | exact resolve b3e38 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e47 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e37 X0 X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e37
          | exact resolve b3e37 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e48 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x x
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b3e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e56 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e47 X0 (M.op x x)
             have i₂ := b3e47 x x
             grind)
          | exact superpose b3e47 b3e47
          | exact resolve b3e47 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e104 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e46 X0 x
             have i₂ := b3e56 (σ y)
             grind)
          | exact superpose b3e56 b3e46
          | exact resolve b3e46 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e56
        have b3e120 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e104 (σ x)
             grind)
          | exact superpose b3e104 b3e19
          | exact resolve b3e19 b3e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104
        have b3e259 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e30 x
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e30
          | (have j1 := b3e53 y
             grind)
          | exact resolve b3e30 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e53
        have b3e266 : y = (M.op y y) := by
          first
          | (have r₁ := b3e259
             have r₂ := b3e120
             grind)
          | exact resolve b3e259 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120 b3e259
        have b3e269 : False := by grind
        exact b3e269
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e54 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e55 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e55 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55
          have b4e61 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e54 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e439 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e60 (σ X0)
               grind)
            | exact superpose b4e60 b4e19
            | (have j1 := b4e60 (σ X0)
               grind)
            | exact resolve b4e19 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e9017 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e439 y
               grind)
            | exact superpose b4e439 b4e23
            | (have j1 := b4e439 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e439 y
               grind)
            | exact resolve b4e23 b4e439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e439
          have b4e9047 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e9017
          have b4e9058 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e9047
               grind)
            | exact superpose b4e9047 b4e20
            | exact resolve b4e20 b4e9047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9047
          have b4e10544 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e9058
               have i₂ := b4e61 y
               grind)
            | exact superpose b4e61 b4e9058
            | (have j1 := b4e61 y
               grind)
            | exact resolve b4e9058 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e9058
          have b4e10556 : y = (M.op y y) := by grind
          clear b4e10544
          have b4e10560 : False := by grind
          exact b4e10560
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b5e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
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
          have b5e30 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 x
               have i₂ := b5e26 (τ X0)
               grind)
            | exact superpose b5e26 b5e27
            | exact resolve b5e27 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e27
          have b5e34 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e30
            | exact resolve b5e30 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e78 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) x
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e83 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e293 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e83 (σ x)
               grind)
            | exact superpose b5e83 b5e34
            | (have j1 := b5e83 (σ x)
               grind)
            | exact resolve b5e34 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e83
          have b5e296 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e293
          have b5e300 : False := by grind
          exact b5e300
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e72 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e89 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e72 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e1173 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e89 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e1174 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e1173 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1173
        have b6e1175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e1174 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1174
        have b6e1842 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e32 y
             have i₂ := b6e1175 y
             grind)
          | exact superpose b6e1175 b6e32
          | (have j1 := b6e1175 y
             grind)
          | exact resolve b6e32 b6e1175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e1175
        have b6e1844 : y = (M.op y y) := by grind
        clear b6e1842
        have b6e1882 : False := by grind
        exact b6e1882
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b7e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e30 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e26 (σ X0)
               grind)
            | exact superpose b7e26 b7e19
            | exact resolve b7e19 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e14 (k X0 x)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e34 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 X1
               have i₂ := b7e18 X2 X0
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X0 X1
               have j1 := b7e18 X1 X1
               grind)
            | (have r₁ := b7e17 X1 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e86 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e65 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e1280 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e86 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e1281 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e1280 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1280
          have b7e1282 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e1281 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1281
          have b7e1985 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 x
               have i₂ := b7e1282 x
               grind)
            | exact superpose b7e1282 b7e34
            | (have j1 := b7e1282 x
               grind)
            | exact resolve b7e34 b7e1282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e1282
          have b7e1987 : x = (M.op x x) := by grind
          clear b7e1985
          have b7e2025 : False := by grind
          exact b7e2025
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e69 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e69 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e254 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e74 (σ X0)
               grind)
            | exact superpose b8e74 b8e19
            | (have j1 := b8e74 (σ X0)
               grind)
            | exact resolve b8e19 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e7219 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e254 x
               grind)
            | exact superpose b8e254 b8e20
            | (have j1 := b8e254 x
               grind)
            | exact resolve b8e20 b8e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e254
          have b8e7334 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e7219
               have r₂ := b8e24
               grind)
            | exact resolve b8e7219 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7219
          have b8e7346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e7334
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e7334
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e7334 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7334
          have b8e7365 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e7346
          have b8e7372 : y = (M.op y y) := by
            first
            | (have r₁ := b8e7365
               have r₂ := b8e22
               grind)
            | exact resolve b8e7365 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7365
          have b8e7373 : False := by grind
          exact b8e7373

/-- `Equation1264`: `x = x ◇ (((y ◇ z) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation1264 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1264 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1264.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
           have i₂ := b0e11 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
        intro X0 X3
        first
        | (have i₁ := b0e31 X0 x x X3
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e31
        | exact resolve b0e31 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e36 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e32 y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e32 (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e32
        | exact resolve b0e32 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e77 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 (σ x)
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e80 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e77
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e77
        | exact resolve b0e77 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e77
      have b0e81 : False := by grind
      exact b0e81
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
             have i₂ := b1e12 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
          intro X0 X3
          first
          | (have i₁ := b1e29 X0 x x X3
             have i₂ := b1e12 X0 x x
             grind)
          | exact superpose b1e12 b1e29
          | exact resolve b1e29 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e43 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b1e44 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 X0 (σ x)
             grind)
          | (have r₁ := b1e15 X0 (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X1 (M.op X0 X0)
             have i₂ := b1e30 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e30 b1e15
          | (have j0 := b1e15 X1 (M.op X0 X0)
             grind)
          | (have r₁ := b1e15 X0 (M.op X0 X0)
             have r₂ := b1e30 X0 (M.op X0 X0)
             grind)
          | exact resolve b1e15 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e47 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e46 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e44 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e86 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X1 X0
             have i₂ := b1e17 X0 X2
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X1 X0
             have j1 := b1e17 X2 X2
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X0
             have r₂ := b1e17 X0 X1
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e92 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e86 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e117 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e50 (σ y)
             grind)
          | exact superpose b1e50 b1e21
          | exact resolve b1e21 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e118 : (σ x) = (k (σ x) y) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e50 (σ x)
             grind)
          | exact superpose b1e50 b1e22
          | exact resolve b1e22 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 x
             have i₂ := b1e49 (σ X0)
             grind)
          | exact superpose b1e49 b1e18
          | exact resolve b1e18 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e138 : ∀ X0 : G, (k (σ X0) y) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e136 X0
             have i₂ := b1e50 (σ X0)
             grind)
          | exact superpose b1e50 b1e136
          | exact resolve b1e136 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50 b1e136
        have b1e449 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e117
             have i₂ := b1e138 y
             grind)
          | exact superpose b1e138 b1e117
          | exact resolve b1e117 b1e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e117
        have b1e450 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e118
             have i₂ := b1e138 x
             grind)
          | exact superpose b1e138 b1e118
          | exact resolve b1e118 b1e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118 b1e138
        have b1e676 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e92 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92
        have b1e677 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e676 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e676
        have b1e684 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e677 X0
             have j1 := b1e15 X0 X0
             grind)
          | (have r₁ := b1e677 x
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e677 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e677
        have b1e877 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e450
             grind)
          | exact superpose b1e450 b1e13
          | exact resolve b1e13 b1e450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e450
        have b1e879 : x = (k x x) := by
          first
          | (have i₁ := b1e877
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e877
          | exact resolve b1e877 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e877
        have b1e883 : x = (M.op x x) := by
          first
          | (have i₁ := b1e879
             have i₂ := b1e684 x
             grind)
          | exact superpose b1e684 b1e879
          | exact resolve b1e879 b1e684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e684 b1e879
        have b1e1030 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e47 x X0
             have i₂ := b1e883
             grind)
          | exact superpose b1e883 b1e47
          | exact resolve b1e47 b1e883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e883
        have b1e1610 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e449
             have i₂ := b1e1030 y
             grind)
          | exact superpose b1e1030 b1e449
          | exact resolve b1e449 b1e1030
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e449 b1e1030
        have b1e1611 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1610
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1610
          | exact resolve b1e1610 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1610
        have b1e1612 : False := by grind
        exact b1e1612
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e40 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b2e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e70 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e45 (σ y)
             grind)
          | exact superpose b2e45 b2e21
          | exact resolve b2e21 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e85 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e85 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e722 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e94 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e723 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e722 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e722
        have b2e729 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e723 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e723 x
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e723 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e723
        have b2e758 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e729 (σ X0)
             grind)
          | exact superpose b2e729 b2e18
          | exact resolve b2e18 b2e729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e761 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e758 X0
             have i₂ := b2e729 X0
             grind)
          | exact superpose b2e729 b2e758
          | exact resolve b2e758 b2e729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e729 b2e758
        have b2e765 : ∀ X0 : G, (k (σ X0) y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e761 X0
             have i₂ := b2e45 (σ X0)
             grind)
          | exact superpose b2e45 b2e761
          | exact resolve b2e761 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45 b2e761
        have b2e1875 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e70
             have i₂ := b2e765 y
             grind)
          | exact superpose b2e765 b2e70
          | exact resolve b2e70 b2e765
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70 b2e765
        have b2e1892 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1875
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1875
          | exact resolve b2e1875 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1875
        have b2e1893 : False := by grind
        exact b2e1893
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | (have r₁ := b3e15 X0 x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b3e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e44 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b3e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e86 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X0 X2
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X2 X2
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e90 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e86 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e114 : (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e50 (σ y)
             grind)
          | exact superpose b3e50 b3e22
          | exact resolve b3e22 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e132 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e49 (σ X0)
             grind)
          | exact superpose b3e49 b3e18
          | exact resolve b3e18 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e134 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e132 X0
             have i₂ := b3e50 (σ X0)
             grind)
          | exact superpose b3e50 b3e132
          | exact resolve b3e132 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132
        have b3e571 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e90 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e572 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e571 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e571
        have b3e578 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e572 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e572 x
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e572 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e572
        have b3e610 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 (τ X0)
             have i₂ := b3e578 (τ X0)
             grind)
          | exact superpose b3e578 b3e23
          | exact resolve b3e23 b3e578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e611 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e610 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e610
          | exact resolve b3e610 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e610
        have b3e615 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b3e611 X0
             have i₂ := b3e50 (τ X0)
             grind)
          | exact superpose b3e50 b3e611
          | exact resolve b3e611 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e611
        have b3e619 : ∀ X0 : G, (k X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e615 X0
             have i₂ := b3e23 X0 x
             grind)
          | exact superpose b3e23 b3e615
          | exact resolve b3e615 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e615
        have b3e763 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e578 X0
             have i₂ := b3e619 X0
             grind)
          | (have i₁ := b3e578 (σ x)
             have i₂ := b3e619 (σ x)
             grind)
          | exact superpose b3e619 b3e578
          | exact resolve b3e578 b3e619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e994 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e50 X0
             have i₂ := b3e763 X0
             grind)
          | exact superpose b3e763 b3e50
          | exact resolve b3e50 b3e763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1017 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e763 (σ X0)
             grind)
          | exact superpose b3e763 b3e18
          | exact resolve b3e18 b3e763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e763
        have b3e1022 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e1017 X0
             have i₂ := b3e50 (σ X0)
             grind)
          | exact superpose b3e50 b3e1017
          | exact resolve b3e1017 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e1017
        have b3e1048 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e1022 X0
             have i₂ := b3e134 X0
             grind)
          | exact superpose b3e134 b3e1022
          | exact resolve b3e1022 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1022
        have b3e1220 : ∀ X0 : G, (k X0 x) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e619 X0
             have i₂ := b3e994 X0
             grind)
          | exact superpose b3e994 b3e619
          | exact resolve b3e619 b3e994
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e619 b3e994
        have b3e1433 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 (τ X0)
             have i₂ := b3e1220 (τ X0)
             grind)
          | (have i₁ := b3e23 X0 x
             have i₂ := b3e1220 (τ X0)
             grind)
          | exact superpose b3e1220 b3e23
          | exact resolve b3e23 b3e1220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1220
        have b3e1436 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b3e1433 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1433
          | exact resolve b3e1433 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1433
        have b3e1441 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b3e1436 X0
             have i₂ := b3e1048 (τ X0)
             grind)
          | exact superpose b3e1048 b3e1436
          | exact resolve b3e1436 b3e1048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1048 b3e1436
        have b3e1443 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e1441 X0
             have i₂ := b3e23 X0 y
             grind)
          | exact superpose b3e23 b3e1441
          | exact resolve b3e1441 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1441
        have b3e1716 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e1443 (σ X0)
             grind)
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e1443 (σ X0)
             grind)
          | exact superpose b3e1443 b3e18
          | exact resolve b3e18 b3e1443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1443
        have b3e1721 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1716 X0
             have i₂ := b3e578 X0
             grind)
          | exact superpose b3e578 b3e1716
          | exact resolve b3e1716 b3e578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e578 b3e1716
        have b3e1729 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1721 X0
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e1721
          | exact resolve b3e1721 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1721
        have b3e1964 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e114
             have i₂ := b3e134 y
             grind)
          | exact superpose b3e134 b3e114
          | exact resolve b3e114 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114 b3e134
        have b3e1971 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1964
             have i₂ := b3e1729 y
             grind)
          | exact superpose b3e1729 b3e1964
          | exact resolve b3e1964 b3e1729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1729 b3e1964
        have b3e2141 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e1971
             grind)
          | exact superpose b3e1971 b3e13
          | exact resolve b3e13 b3e1971
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1971
        have b3e2142 : y = (M.op y y) := by
          first
          | (have i₁ := b3e2141
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2141
          | exact resolve b3e2141 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2141
        have b3e2146 : False := by grind
        exact b3e2146
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
               have i₂ := b4e13 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b4e35 X0 x x X3
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e40 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e36 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e40 x
               grind)
            | exact superpose b4e40 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e40 x
               grind)
            | exact resolve b4e17 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e70 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e69 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e73 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e66 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e263 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e73 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e73 X0
               grind)
            | exact resolve b4e16 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e265 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e36
            | (have j1 := b4e73 X0
               grind)
            | exact resolve b4e36 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e73
          have b4e278 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e263 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e263
          have b4e10288 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e278 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e278
          have b4e10293 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e10288 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e10288
            | (have j0 := b4e10288 X0
               grind)
            | exact resolve b4e10288 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10288
          have b4e10353 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e10293 X0
               have j1 := b4e265 X0 x
               grind)
            | (have r₁ := b4e10293 X0
               have r₂ := b4e265 X0 (σ x)
               grind)
            | exact resolve b4e10293 b4e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e265 b4e10293
          have b4e10412 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e10353 (σ X0)
               grind)
            | exact superpose b4e10353 b4e19
            | exact resolve b4e19 b4e10353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10353
          have b4e14713 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e10412 y
               grind)
            | exact superpose b4e10412 b4e20
            | exact resolve b4e20 b4e10412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10412
          have b4e68330 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e14713
               have i₂ := b4e70 y
               grind)
            | exact superpose b4e70 b4e14713
            | (have j1 := b4e70 y
               grind)
            | exact resolve b4e14713 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e14713
          have b4e68408 : y = (M.op y y) := by grind
          clear b4e68330
          have b4e68439 : False := by grind
          exact b4e68439
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e46 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e77 : (σ x) ≠ (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e51 (σ x)
               grind)
            | exact superpose b5e51 b5e24
            | exact resolve b5e24 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e101 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e91 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e689 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e101 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101
          have b5e690 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e689 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e689
          have b5e696 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e690 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e690 x
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e690 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e690
          have b5e723 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e696 (σ X0)
               grind)
            | exact superpose b5e696 b5e19
            | exact resolve b5e19 b5e696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e726 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e723 X0
               have i₂ := b5e696 X0
               grind)
            | exact superpose b5e696 b5e723
            | exact resolve b5e723 b5e696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e696 b5e723
          have b5e730 : ∀ X0 : G, (k (σ X0) x) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e726 X0
               have i₂ := b5e51 (σ X0)
               grind)
            | exact superpose b5e51 b5e726
            | exact resolve b5e726 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e726
          have b5e2104 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e77
               have i₂ := b5e730 x
               grind)
            | exact superpose b5e730 b5e77
            | exact resolve b5e77 b5e730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e730
          have b5e2121 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e2104
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2104
            | exact resolve b5e2104 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2104
          have b5e2122 : False := by grind
          exact b5e2122
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
             have i₂ := b6e12 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
          intro X0 X3
          first
          | (have i₁ := b6e28 X0 x x X3
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e28
          | exact resolve b6e28 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e29 (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b6e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X0 X2
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X2 X2
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e69 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e90 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e29 X0 (M.op X0 X0)
             have i₂ := b6e45 (M.op X0 X0)
             grind)
          | exact superpose b6e45 b6e29
          | exact resolve b6e29 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e45
        have b6e360 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e90 (σ y)
             have i₂ := b6e32 (σ y)
             grind)
          | exact superpose b6e32 b6e90
          | exact resolve b6e90 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e90
        have b6e366 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e360
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e360
          | exact resolve b6e360 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e360
        have b6e450 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e73 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e451 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e450 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e450
        have b6e455 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e451 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e451 x
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e451 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e451
        have b6e595 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e366
             grind)
          | exact superpose b6e366 b6e13
          | exact resolve b6e13 b6e366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e366
        have b6e597 : y = (k y y) := by
          first
          | (have i₁ := b6e595
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e595
          | exact resolve b6e595 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e595
        have b6e603 : y = (M.op y y) := by
          first
          | (have i₁ := b6e597
             have i₂ := b6e455 y
             grind)
          | exact superpose b6e455 b6e597
          | exact resolve b6e597 b6e455
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e455 b6e597
        have b6e606 : False := by grind
        exact b6e606
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
               have i₂ := b7e13 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b7e34 X0 x x X3
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e38 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e35 (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e46 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e343 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e30 X0 x
               have i₂ := b7e51 X0
               grind)
            | exact superpose b7e51 b7e30
            | exact resolve b7e30 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e51
          have b7e476 : (τ (σ x)) = (k (τ (σ x)) x) := by
            first
            | (have i₁ := b7e343 (σ x)
               have i₂ := b7e38 (σ x)
               grind)
            | exact superpose b7e38 b7e343
            | exact resolve b7e343 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e343
          have b7e488 : x = (k x x) := by
            first
            | (have i₁ := b7e476
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e476
            | exact resolve b7e476 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e476
          have b7e614 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e488
               grind)
            | exact superpose b7e488 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e488
          have b7e615 : x = (M.op x x) := by grind
          clear b7e614
          have b7e619 : False := by grind
          exact b7e619
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
               have i₂ := b8e13 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b8e33 X0 x x X3
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e97 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 X0 X1
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e34
            | (have j1 := b8e18 X2 X2
               grind)
            | exact resolve b8e34 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e102 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e102 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e221 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e109 (σ X0)
               grind)
            | exact superpose b8e109 b8e19
            | (have j1 := b8e109 (σ X0)
               grind)
            | exact resolve b8e19 b8e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e9487 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e221 x
               grind)
            | exact superpose b8e221 b8e20
            | (have j1 := b8e221 x
               grind)
            | exact resolve b8e20 b8e221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e221
          have b8e9691 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e9487
               have r₂ := b8e24
               grind)
            | exact resolve b8e9487 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9487
          have b8e9757 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = X0 ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e9691
               have i₂ := b8e97 y X0 x
               grind)
            | exact superpose b8e97 b8e9691
            | (have j1 := b8e97 y X0 x
               grind)
            | exact resolve b8e9691 b8e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97 b8e9691
          have b8e9764 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
            intro X0
            first
            | (have j0 := b8e9757 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9757
          have b8e9771 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b8e9764 X0
               grind)
            | (have r₁ := b8e9764 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e9764 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9764
          have b8e10075 : y ≠ y := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e9771 y
               grind)
            | exact superpose b8e9771 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e9771 y
               grind)
            | exact resolve b8e21 b8e9771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9771
          have b8e10076 : False := by grind
          exact b8e10076

/-- `Equation1271`: `x = x ◇ (((y ◇ z) ◇ w) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pxy_pyx_Equation1271 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1271 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1271.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
           have i₂ := b0e11 (M.op X0 X1) x x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X0 (M.op (M.op x x) x) X1
           have i₂ := b0e30 x x X0
           grind)
        | exact superpose b0e30 b0e30
        | exact resolve b0e30 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e68 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e35
        | exact resolve b0e35 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e170 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e69 (σ x)
           grind)
        | exact superpose b0e69 b0e18
        | exact resolve b0e18 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e173 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e170
           have i₂ := b0e68 x
           grind)
        | exact superpose b0e68 b0e170
        | exact resolve b0e170 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68 b0e170
      have b0e174 : False := by grind
      exact b0e174
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e39 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b1e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e56 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e46 (σ y)
             grind)
          | exact superpose b1e46 b1e21
          | exact resolve b1e21 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e112 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e104 X0 X1
             have i₂ := b1e46 (σ X0)
             grind)
          | exact superpose b1e46 b1e104
          | (have j0 := b1e104 X0 X1
             grind)
          | exact resolve b1e104 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104
        have b1e114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e112 X0 X1
             have i₂ := b1e46 (σ X1)
             grind)
          | exact superpose b1e46 b1e112
          | (have j0 := b1e112 X0 X1
             grind)
          | exact resolve b1e112 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112
        have b1e1511 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e114 y y
             grind)
          | exact superpose b1e114 b1e21
          | (have j1 := b1e114 y y
             grind)
          | exact resolve b1e21 b1e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e1564 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b1e1511
        have b1e1597 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e1564
             have r₂ := b1e56
             grind)
          | exact resolve b1e1564 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e1564
        have b1e1621 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1597
             have i₂ := b1e46 y
             grind)
          | exact superpose b1e46 b1e1597
          | exact resolve b1e1597 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e1597
        have b1e1629 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1621
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1621
          | exact resolve b1e1621 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1621
        have b1e1630 : False := by grind
        exact b1e1630
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e37 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b2e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e51 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e42 (σ y)
             grind)
          | exact superpose b2e42 b2e21
          | exact resolve b2e21 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e102 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e94 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e108 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e98 X0 X1
             have i₂ := b2e42 (σ X0)
             grind)
          | exact superpose b2e42 b2e98
          | (have j0 := b2e98 X0 X1
             grind)
          | exact resolve b2e98 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e110 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) y) ∨ (σ X1) = (k (σ X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e108 X0 X1
             have i₂ := b2e42 (σ X1)
             grind)
          | exact superpose b2e42 b2e108
          | (have j0 := b2e108 X0 X1
             grind)
          | exact resolve b2e108 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108
        have b2e693 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e102 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e102
        have b2e694 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e693 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e693
        have b2e702 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e694 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e694 x
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e694 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e694
        have b2e720 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e23 X0 (τ X0)
             have i₂ := b2e702 (τ X0)
             grind)
          | exact superpose b2e702 b2e23
          | exact resolve b2e23 b2e702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e721 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e720 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e720
          | exact resolve b2e720 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e720
        have b2e725 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b2e721 X0
             have i₂ := b2e42 (τ X0)
             grind)
          | exact superpose b2e42 b2e721
          | exact resolve b2e721 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e721
        have b2e729 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e725 X0
             have i₂ := b2e23 X0 y
             grind)
          | exact superpose b2e23 b2e725
          | exact resolve b2e725 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e725
        have b2e909 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e729 (σ X0)
             grind)
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e729 (σ X0)
             grind)
          | exact superpose b2e729 b2e18
          | exact resolve b2e18 b2e729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e729
        have b2e916 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e909 X0
             have i₂ := b2e702 X0
             grind)
          | exact superpose b2e702 b2e909
          | exact resolve b2e909 b2e702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e702 b2e909
        have b2e934 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e916 X0
             have i₂ := b2e18 X0 y
             grind)
          | exact superpose b2e18 b2e916
          | exact resolve b2e916 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e916
        have b2e1604 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e110 y y
             grind)
          | exact superpose b2e110 b2e21
          | (have j1 := b2e110 y y
             grind)
          | exact resolve b2e21 b2e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110
        have b2e1661 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e1604
        have b2e1698 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e1661
             have r₂ := b2e51
             grind)
          | exact resolve b2e1661 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e1661
        have b2e1726 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1698
             have i₂ := b2e934 y
             grind)
          | exact superpose b2e934 b2e1698
          | exact resolve b2e1698 b2e934
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e934 b2e1698
        have b2e1734 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1726
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1726
          | exact resolve b2e1726 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1726
        have b2e1735 : False := by grind
        exact b2e1735
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | (have r₁ := b3e15 X0 x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b3e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b3e39 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e56 : (σ y) = (k (σ y) x) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e46 (σ y)
             grind)
          | exact superpose b3e46 b3e22
          | exact resolve b3e22 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e99 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X0 X2
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X2 X2
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e103 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e99 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e45 (σ X0)
             grind)
          | exact superpose b3e45 b3e18
          | exact resolve b3e18 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e143 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e141 X0
             have i₂ := b3e46 (σ X0)
             grind)
          | exact superpose b3e46 b3e141
          | exact resolve b3e141 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141
        have b3e620 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e103 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e621 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e620 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e620
        have b3e629 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e621 X0
             have j1 := b3e15 X0 X0
             grind)
          | (have r₁ := b3e621 x
             have r₂ := b3e15 X0 x
             grind)
          | exact resolve b3e621 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e621
        have b3e656 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 (τ X0)
             have i₂ := b3e629 (τ X0)
             grind)
          | exact superpose b3e629 b3e23
          | exact resolve b3e23 b3e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e657 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e656 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e656
          | exact resolve b3e656 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e656
        have b3e661 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b3e657 X0
             have i₂ := b3e46 (τ X0)
             grind)
          | exact superpose b3e46 b3e657
          | exact resolve b3e657 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e657
        have b3e665 : ∀ X0 : G, (k X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e661 X0
             have i₂ := b3e23 X0 x
             grind)
          | exact superpose b3e23 b3e661
          | exact resolve b3e661 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e661
        have b3e817 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e629 X0
             have i₂ := b3e665 X0
             grind)
          | (have i₁ := b3e629 (σ x)
             have i₂ := b3e665 (σ x)
             grind)
          | exact superpose b3e665 b3e629
          | exact resolve b3e629 b3e665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1014 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e46 X0
             have i₂ := b3e817 X0
             grind)
          | exact superpose b3e817 b3e46
          | exact resolve b3e46 b3e817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1044 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e817 (σ X0)
             grind)
          | exact superpose b3e817 b3e18
          | exact resolve b3e18 b3e817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e817
        have b3e1049 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e1044 X0
             have i₂ := b3e46 (σ X0)
             grind)
          | exact superpose b3e46 b3e1044
          | exact resolve b3e1044 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46 b3e1044
        have b3e1070 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e1049 X0
             have i₂ := b3e143 X0
             grind)
          | exact superpose b3e143 b3e1049
          | exact resolve b3e1049 b3e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1049
        have b3e1280 : ∀ X0 : G, (k X0 x) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e665 X0
             have i₂ := b3e1014 X0
             grind)
          | exact superpose b3e1014 b3e665
          | exact resolve b3e665 b3e1014
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e665 b3e1014
        have b3e1571 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e23 X0 (τ X0)
             have i₂ := b3e1280 (τ X0)
             grind)
          | (have i₁ := b3e23 X0 x
             have i₂ := b3e1280 (τ X0)
             grind)
          | exact superpose b3e1280 b3e23
          | exact resolve b3e23 b3e1280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1280
        have b3e1574 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b3e1571 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1571
          | exact resolve b3e1571 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1571
        have b3e1579 : ∀ X0 : G, (k X0 X0) = (σ (k (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b3e1574 X0
             have i₂ := b3e1070 (τ X0)
             grind)
          | exact superpose b3e1070 b3e1574
          | exact resolve b3e1574 b3e1070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1070 b3e1574
        have b3e1581 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e1579 X0
             have i₂ := b3e23 X0 y
             grind)
          | exact superpose b3e23 b3e1579
          | exact resolve b3e1579 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1579
        have b3e1786 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e1581 (σ X0)
             grind)
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e1581 (σ X0)
             grind)
          | exact superpose b3e1581 b3e18
          | exact resolve b3e18 b3e1581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1581
        have b3e1791 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1786 X0
             have i₂ := b3e629 X0
             grind)
          | exact superpose b3e629 b3e1786
          | exact resolve b3e1786 b3e629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e629 b3e1786
        have b3e1799 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1791 X0
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e1791
          | exact resolve b3e1791 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1791
        have b3e1881 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e143 y
             grind)
          | exact superpose b3e143 b3e56
          | exact resolve b3e56 b3e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e143
        have b3e1889 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e1881
             have i₂ := b3e1799 y
             grind)
          | exact superpose b3e1799 b3e1881
          | exact resolve b3e1881 b3e1799
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1799 b3e1881
        have b3e1998 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e1889
             grind)
          | exact superpose b3e1889 b3e13
          | exact resolve b3e13 b3e1889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1889
        have b3e1999 : y = (M.op y y) := by
          first
          | (have i₁ := b3e1998
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1998
          | exact resolve b3e1998 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1998
        have b3e2003 : False := by grind
        exact b3e2003
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
            intro X0 X1 X2 X3
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
          have b4e34 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
               have i₂ := b4e13 (M.op X0 X1) x x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X0 (M.op (M.op x x) x) X1
               have i₂ := b4e34 x x X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e45 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | (have r₁ := b4e16 X0 x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e16 X0 (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e62 : (σ y) ≠ (k (σ y) x) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e52 (σ y)
               grind)
            | exact superpose b4e52 b4e23
            | exact resolve b4e23 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ x) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e65 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e72 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e64 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e107 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e114 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e107 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107
          have b4e154 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e51 (σ X0)
               grind)
            | exact superpose b4e51 b4e19
            | exact resolve b4e19 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e158 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e154 X0
               have i₂ := b4e52 (σ X0)
               grind)
            | exact superpose b4e52 b4e154
            | exact resolve b4e154 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154
          have b4e194 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e72 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e72 X0
               grind)
            | exact resolve b4e16 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e196 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0 X1
               have i₂ := b4e72 X0
               grind)
            | exact superpose b4e72 b4e39
            | (have j1 := b4e72 X0
               grind)
            | exact resolve b4e39 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e72
          have b4e207 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0 X1
            first
            | (have j0 := b4e194 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194
          have b4e327 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e71 (σ X0)
               grind)
            | exact superpose b4e71 b4e19
            | (have j1 := b4e71 (σ X0)
               grind)
            | exact resolve b4e19 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e337 : ∀ X0 : G, (σ X0) = (k (σ X0) x) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e327 X0
               have i₂ := b4e52 (σ X0)
               grind)
            | exact superpose b4e52 b4e327
            | (have j0 := b4e327 X0
               grind)
            | exact resolve b4e327 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e327
          have b4e343 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e337 X0
               have i₂ := b4e158 X0
               grind)
            | exact superpose b4e158 b4e337
            | (have j0 := b4e337 X0
               grind)
            | exact resolve b4e337 b4e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e337
          have b4e768 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e114 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114
          have b4e769 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e768 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e768
          have b4e778 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e769 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e769 x
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e769 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e769
          have b4e807 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e25 X0 (τ X0)
               have i₂ := b4e778 (τ X0)
               grind)
            | exact superpose b4e778 b4e25
            | exact resolve b4e25 b4e778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e808 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e807 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e807
            | exact resolve b4e807 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e807
          have b4e812 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e808 X0
               have i₂ := b4e52 (τ X0)
               grind)
            | exact superpose b4e52 b4e808
            | exact resolve b4e808 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e808
          have b4e816 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e812 X0
               have i₂ := b4e25 X0 x
               grind)
            | exact superpose b4e25 b4e812
            | exact resolve b4e812 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e812
          have b4e1003 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e816 (σ X0)
               grind)
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e816 (σ X0)
               grind)
            | exact superpose b4e816 b4e19
            | exact resolve b4e19 b4e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e816
          have b4e1009 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1003 X0
               have i₂ := b4e778 X0
               grind)
            | exact superpose b4e778 b4e1003
            | exact resolve b4e1003 b4e778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e778 b4e1003
          have b4e1015 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1009 X0
               have i₂ := b4e19 X0 x
               grind)
            | exact superpose b4e19 b4e1009
            | exact resolve b4e1009 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1009
          have b4e1376 : (σ y) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b4e62
               have i₂ := b4e158 y
               grind)
            | exact superpose b4e158 b4e62
            | exact resolve b4e62 b4e158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e158
          have b4e1386 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1376
               have i₂ := b4e1015 y
               grind)
            | exact superpose b4e1015 b4e1376
            | exact resolve b4e1376 b4e1015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1376
          have b4e7242 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e207 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e207
          have b4e7247 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e7242 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e7242
            | (have j0 := b4e7242 X0
               grind)
            | exact resolve b4e7242 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7242
          have b4e7284 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e7247 X0
               have j1 := b4e196 X0 x
               grind)
            | (have r₁ := b4e7247 X0
               have r₂ := b4e196 X0 x
               grind)
            | exact resolve b4e7247 b4e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196 b4e7247
          have b4e19855 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e343 y
               grind)
            | exact superpose b4e343 b4e20
            | (have j1 := b4e343 y
               grind)
            | exact resolve b4e20 b4e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343
          have b4e20001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e19855
               have i₂ := b4e7284 y
               grind)
            | exact superpose b4e7284 b4e19855
            | exact resolve b4e19855 b4e7284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7284 b4e19855
          have b4e20002 : (σ y) = (σ (k y x)) := by grind
          clear b4e20001
          have b4e20060 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20002
               have i₂ := b4e1015 y
               grind)
            | exact superpose b4e1015 b4e20002
            | exact resolve b4e20002 b4e1015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1015 b4e20002
          have b4e20072 : False := by grind
          exact b4e20072
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e43 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e16 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 X0 x
               grind)
            | (have r₁ := b5e16 X0 x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e58 : (σ x) ≠ (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e48 (σ x)
               grind)
            | exact superpose b5e48 b5e24
            | exact resolve b5e24 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e100 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X0 X2
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b5e109 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e100 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e116 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) x) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e104 X0 X1
               have i₂ := b5e48 (σ X0)
               grind)
            | exact superpose b5e48 b5e104
            | (have j0 := b5e104 X0 X1
               grind)
            | exact resolve b5e104 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (k (σ X0) x) ∨ (σ X1) = (k (σ X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e116 X0 X1
               have i₂ := b5e48 (σ X1)
               grind)
            | exact superpose b5e48 b5e116
            | (have j0 := b5e116 X0 X1
               grind)
            | exact resolve b5e116 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116
          have b5e625 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e109 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109
          have b5e626 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e625 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e625
          have b5e634 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e626 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e626 x
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e626 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e626
          have b5e652 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e25 X0 (τ X0)
               have i₂ := b5e634 (τ X0)
               grind)
            | exact superpose b5e634 b5e25
            | exact resolve b5e25 b5e634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e653 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e652 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e652
            | exact resolve b5e652 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e652
          have b5e657 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e653 X0
               have i₂ := b5e48 (τ X0)
               grind)
            | exact superpose b5e48 b5e653
            | exact resolve b5e653 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e653
          have b5e661 : ∀ X0 : G, (k X0 (σ x)) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e657 X0
               have i₂ := b5e25 X0 x
               grind)
            | exact superpose b5e25 b5e657
            | exact resolve b5e657 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e657
          have b5e835 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e661 (σ X0)
               grind)
            | (have i₁ := b5e19 X0 x
               have i₂ := b5e661 (σ X0)
               grind)
            | exact superpose b5e661 b5e19
            | exact resolve b5e19 b5e661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e661
          have b5e842 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e835 X0
               have i₂ := b5e634 X0
               grind)
            | exact superpose b5e634 b5e835
            | exact resolve b5e835 b5e634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e634 b5e835
          have b5e860 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e842 X0
               have i₂ := b5e19 X0 x
               grind)
            | exact superpose b5e19 b5e842
            | exact resolve b5e842 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842
          have b5e1514 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) ∨ (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e118 x x
               grind)
            | exact superpose b5e118 b5e24
            | (have j1 := b5e118 x x
               grind)
            | exact resolve b5e24 b5e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e1567 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) x) := by grind
          clear b5e1514
          have b5e1603 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b5e1567
               have r₂ := b5e58
               grind)
            | exact resolve b5e1567 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e1567
          have b5e1630 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1603
               have i₂ := b5e860 x
               grind)
            | exact superpose b5e860 b5e1603
            | exact resolve b5e1603 b5e860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e860 b5e1603
          have b5e1639 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1630
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1630
            | exact resolve b5e1630 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1630
          have b5e1640 : False := by grind
          exact b5e1640
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X3) X1)) = X0 := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
             have i₂ := b6e12 (M.op X0 X1) x x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e27 X0 (M.op (M.op x x) x) X1
             have i₂ := b6e27 x x X0
             grind)
          | exact superpose b6e27 b6e27
          | exact resolve b6e27 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b6e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e43 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e31
          | exact resolve b6e31 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e82 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X0 X2
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X2 X2
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e87 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e82 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e42 (σ X0)
             grind)
          | exact superpose b6e42 b6e18
          | exact resolve b6e18 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e631 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e87 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e632 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e631 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e631
        have b6e638 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e632 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e632 x
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e632 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e632
        have b6e1453 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e43 (σ y)
             have i₂ := b6e109 y
             grind)
          | exact superpose b6e109 b6e43
          | exact resolve b6e43 b6e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e109
        have b6e1487 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e1453
             have i₂ := b6e638 y
             grind)
          | exact superpose b6e638 b6e1453
          | exact resolve b6e1453 b6e638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e638 b6e1453
        have b6e1792 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e1487
             grind)
          | exact superpose b6e1487 b6e13
          | exact resolve b6e13 b6e1487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1487
        have b6e1803 : y = (M.op y y) := by
          first
          | (have i₁ := b6e1792
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1792
          | exact resolve b6e1792 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1792
        have b6e1805 : False := by grind
        exact b6e1805
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
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
          have b7e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 X0 (σ x)
               grind)
            | (have r₁ := b7e16 X0 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b7e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e88 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X0 X2
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X2 X2
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e88 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e48 (σ X0)
               grind)
            | exact superpose b7e48 b7e19
            | exact resolve b7e19 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e721 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e96 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e722 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e721 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e721
          have b7e729 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e722 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e722 x
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e722 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e722
          have b7e1538 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b7e30 (σ X0) X0
               have i₂ := b7e729 (σ X0)
               grind)
            | exact superpose b7e729 b7e30
            | exact resolve b7e30 b7e729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e1558 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (σ (k X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e1538 X0
               have i₂ := b7e119 X0
               grind)
            | exact superpose b7e119 b7e1538
            | exact resolve b7e1538 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119 b7e1538
          have b7e1562 : ∀ X0 : G, (k X0 x) = (k (τ (σ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b7e1558 X0
               have i₂ := b7e14 (k X0 x)
               grind)
            | exact superpose b7e14 b7e1558
            | exact resolve b7e1558 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1558
          have b7e1565 : ∀ X0 : G, (k X0 x) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e1562 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e1562
            | exact resolve b7e1562 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1562
          have b7e1985 : (M.op (σ x) (σ x)) = (k (σ x) x) := by
            first
            | (have i₁ := b7e48 (σ x)
               have i₂ := b7e1565 (σ x)
               grind)
            | exact superpose b7e1565 b7e48
            | exact resolve b7e48 b7e1565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e1989 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e1565 (σ X0)
               grind)
            | exact superpose b7e1565 b7e19
            | exact resolve b7e19 b7e1565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1565
          have b7e1997 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b7e1989 X0
               have i₂ := b7e729 X0
               grind)
            | exact superpose b7e729 b7e1989
            | exact resolve b7e1989 b7e729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e729 b7e1989
          have b7e2000 : (σ x) = (k (σ x) x) := by
            first
            | (have i₁ := b7e1985
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1985
            | exact resolve b7e1985 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1985
          have b7e2026 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e2000
               have i₂ := b7e1997 x
               grind)
            | exact superpose b7e1997 b7e2000
            | exact resolve b7e2000 b7e1997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1997 b7e2000
          have b7e2333 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e2026
               grind)
            | exact superpose b7e2026 b7e14
            | exact resolve b7e14 b7e2026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2026
          have b7e2348 : x = (M.op x x) := by
            first
            | (have i₁ := b7e2333
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2333
            | exact resolve b7e2333 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2333
          have b7e2351 : False := by grind
          exact b7e2351
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e98 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) X0
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) x
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e98 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98
          have b8e293 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e103 (σ X0)
               grind)
            | exact superpose b8e103 b8e19
            | (have j1 := b8e103 (σ X0)
               grind)
            | exact resolve b8e19 b8e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e8607 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e293 x
               grind)
            | exact superpose b8e293 b8e20
            | (have j1 := b8e293 x
               grind)
            | exact resolve b8e20 b8e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293
          have b8e8780 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e8607
               have r₂ := b8e24
               grind)
            | exact resolve b8e8607 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8607
          have b8e8826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e8780
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e8780
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e8780 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8780
          have b8e8839 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e8826
          have b8e8846 : y = (M.op y y) := by
            first
            | (have r₁ := b8e8839
               have r₂ := b8e22
               grind)
            | exact resolve b8e8839 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8839
          have b8e8847 : False := by grind
          exact b8e8847
