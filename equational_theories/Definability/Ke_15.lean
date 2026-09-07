import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pyx_Equation4393 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e61 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e64 : False := by grind
      exact b0e64
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
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
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
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
          have b4e39 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e35 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e40 : y = (σ y) := by
            first
            | (have i₁ := b4e39 x
               have i₂ := b4e38 x
               grind)
            | exact superpose b4e38 b4e39
            | exact resolve b4e39 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e67 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = y := by
            intro X1 X2
            first
            | (have i₁ := b4e13 x X1 X2
               have i₂ := b4e38 x
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e717 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e59 x y
               grind)
            | exact superpose b4e59 b4e20
            | (have j1 := b4e59 x y
               grind)
            | exact resolve b4e20 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e734 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e717
               have r₂ := b4e23
               grind)
            | exact resolve b4e717 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e717
          have b4e741 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e734
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e734
            | exact resolve b4e734 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e734
          have b4e1209 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e741
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e741
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e741
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e741
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e741 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e741
          have b4e1210 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e1209
          have b4e1211 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1210
               have r₂ := b4e21
               grind)
            | exact resolve b4e1210 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1210
          have b4e2610 : y = (M.op (σ x) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e67 (σ x) y
               have i₂ := b4e1211
               grind)
            | exact superpose b4e1211 b4e67
            | exact resolve b4e67 b4e1211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2673 : y = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1211
               have i₂ := b4e2610
               grind)
            | exact superpose b4e2610 b4e1211
            | exact resolve b4e1211 b4e2610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1211 b4e2610
          have b4e2681 : x = (M.op x y) ∨ y = (σ x) := by grind
          clear b4e2673
          have b4e2787 : y = (M.op x y) ∨ y = (σ x) := by
            first
            | (have i₁ := b4e67 x y
               have i₂ := b4e2681
               grind)
            | exact superpose b4e2681 b4e67
            | exact resolve b4e67 b4e2681
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e2890 : x = y ∨ y = (σ x) ∨ y = (σ x) := by
            first
            | (have i₁ := b4e2681
               have i₂ := b4e2787
               grind)
            | exact superpose b4e2787 b4e2681
            | exact resolve b4e2681 b4e2787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2681 b4e2787
          have b4e2899 : x = y ∨ y = (σ x) := by grind
          clear b4e2890
          have b4e2907 : y = (σ x) := by
            first
            | (have r₁ := b4e2899
               have r₂ := b4e21
               grind)
            | exact resolve b4e2899 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2899
          have b4e3009 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e2907
               grind)
            | exact superpose b4e2907 b4e23
            | exact resolve b4e23 b4e2907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2907
          have b4e3049 : False := by grind
          exact b4e3049
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
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
          have b5e37 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
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
          have b5e39 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = y := by
            intro X1 X2
            first
            | (have i₁ := b5e13 x X1 X2
               have i₂ := b5e37 x
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : ∀ X1 : G, y = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b5e39 (M.op x X1) X1
               have i₂ := b5e39 x X1
               grind)
            | exact superpose b5e39 b5e39
            | exact resolve b5e39 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e102 : ∀ X0 : G, y = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e37 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e37
            | exact resolve b5e37 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e112 : y = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e102 y
               have i₂ := b5e57 y
               grind)
            | exact superpose b5e57 b5e102
            | exact resolve b5e102 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e118 : y = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e112
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e112
            | exact resolve b5e112 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e112
          have b5e123 : y = (σ y) := by
            first
            | (have i₁ := b5e118
               have i₂ := b5e57 y
               grind)
            | exact superpose b5e57 b5e118
            | exact resolve b5e118 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e203 : y ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e123
               grind)
            | exact superpose b5e123 b5e24
            | exact resolve b5e24 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123
          have b5e210 : False := by grind
          exact b5e210
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ x)) := by
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
          have b7e37 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e33 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e39 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (σ y) := by
            intro X1 X2
            first
            | (have i₁ := b7e13 x X1 X2
               have i₂ := b7e37 x
               grind)
            | exact superpose b7e37 b7e13
            | exact resolve b7e13 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e55 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) := by
            intro X1
            first
            | (have i₁ := b7e39 (M.op x X1) X1
               have i₂ := b7e39 x X1
               grind)
            | exact superpose b7e39 b7e39
            | exact resolve b7e39 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e123 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e55 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e55
            | exact resolve b7e55 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e136 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e123
               grind)
            | exact superpose b7e123 b7e14
            | exact resolve b7e14 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123
          have b7e137 : y = (M.op y y) := by
            first
            | (have i₁ := b7e136
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e136
            | exact resolve b7e136 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e221 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e39 y y
               have i₂ := b7e137
               grind)
            | exact superpose b7e137 b7e39
            | exact resolve b7e39 b7e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e224 : y = (σ y) := by
            first
            | (have i₁ := b7e221
               have i₂ := b7e137
               grind)
            | exact superpose b7e137 b7e221
            | exact resolve b7e221 b7e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e137 b7e221
          have b7e282 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e55 x
               have i₂ := b7e224
               grind)
            | exact superpose b7e224 b7e55
            | exact resolve b7e55 b7e224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55 b7e224
          have b7e615 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e282 x
               grind)
            | exact superpose b7e282 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e282 x
               grind)
            | exact resolve b7e22 b7e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e282
          have b7e632 : False := by grind
          exact b7e632
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b8e13 x X3 X4
               have i₂ := b8e13 x X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e13 X1 x x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e26
          have b8e41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e37 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e37
            | exact resolve b8e37 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e41
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e63 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (σ X0) X1 X2
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X0 X1) X1) X5) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b8e32 X2 X3 (M.op x X5) X5
               have i₂ := b8e32 x X5 X0 X1
               grind)
            | (have i₁ := b8e32 X2 X3 (M.op x X5) X5
               have i₂ := b8e32 X0 X1 x X5
               grind)
            | exact superpose b8e32 b8e32
            | exact resolve b8e32 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op X0 (M.op X0 X0)) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e32 X1 X2 (M.op x X4) X4
               have i₂ := b8e13 X0 x X4
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e86 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b8e13 X2 (M.op x X4) X4
               have i₂ := b8e32 x X4 X0 X1
               grind)
            | (have i₁ := b8e13 X2 (M.op x X4) X4
               have i₂ := b8e32 X0 X1 x X4
               grind)
            | exact superpose b8e32 b8e13
            | exact resolve b8e13 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e124 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e14
            | exact resolve b8e14 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42
          have b8e308 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 (τ X0) (τ X0) X1 X2
               have i₂ := b8e124 X0
               grind)
            | exact superpose b8e124 b8e32
            | exact resolve b8e32 b8e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e309 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (τ X0) (τ X0)
               have i₂ := b8e124 X0
               grind)
            | exact superpose b8e124 b8e13
            | exact resolve b8e13 b8e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e321 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e58 x y
               grind)
            | exact superpose b8e58 b8e20
            | (have j1 := b8e58 x y
               grind)
            | exact resolve b8e20 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e332 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e321
               have r₂ := b8e23
               grind)
            | exact resolve b8e321 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e321
          have b8e501 : ∀ X0 X1 X2 X3 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (M.op (M.op (M.op X1 X2) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e75 X1 X2 (τ X0) (τ X0) X3
               have i₂ := b8e124 X0
               grind)
            | exact superpose b8e124 b8e75
            | exact resolve b8e75 b8e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e561 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op (M.op X3 X4) X4) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X6) := by
            intro X0 X1 X2 X3 X4 X6
            first
            | (have i₁ := b8e32 X3 X4 (M.op x X6) X6
               have i₂ := b8e75 X0 X1 x X6 X2
               grind)
            | (have i₁ := b8e32 X0 X1 (M.op (M.op X0 X1) X1) x
               have i₂ := b8e75 X0 X1 X2 X3 x
               grind)
            | exact superpose b8e75 b8e32
            | exact resolve b8e32 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e581 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (σ (M.op (M.op X4 X5) X5)) (σ (M.op (M.op X0 X1) X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e63 (M.op (M.op X4 X5) X5) X2 X3
               have i₂ := b8e75 X4 X5 X0 X1 (M.op (M.op X4 X5) X5)
               grind)
            | exact superpose b8e75 b8e63
            | exact resolve b8e63 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63 b8e75
          have b8e846 : ∀ X0 X1 X2 X4 X5 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) X1) X4) X5) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b8e86 (M.op x X4) X4 X2 X5
               have i₂ := b8e76 X0 x X4 X1
               grind)
            | (have i₁ := b8e86 (M.op X0 (M.op X0 X0)) X4 X2 X4
               have i₂ := b8e76 X0 X1 X2 X4
               grind)
            | exact superpose b8e76 b8e86
            | exact resolve b8e86 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e86
          have b8e1338 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e308 (τ X0) X1 X2
               have i₂ := b8e124 X0
               grind)
            | exact superpose b8e124 b8e308
            | exact resolve b8e308 b8e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e308
          have b8e1456 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (τ (τ (M.op X0 X0))) (τ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e309 (τ X0) X1
               have i₂ := b8e124 X0
               grind)
            | exact superpose b8e124 b8e309
            | exact resolve b8e309 b8e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309
          have b8e5572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e332
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e332
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e332
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e332
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e332 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e332
          have b8e5573 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e5572
          have b8e5574 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e5573
               have r₂ := b8e21
               grind)
            | exact resolve b8e5573 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5573
          have b8e5577 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 (σ x) (σ y)
               have i₂ := b8e5574
               grind)
            | exact superpose b8e5574 b8e13
            | exact resolve b8e13 b8e5574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35556 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e5574
               have i₂ := b8e5577 X0
               grind)
            | exact superpose b8e5577 b8e5574
            | exact resolve b8e5574 b8e5577
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5574 b8e5577
          have b8e35603 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ x) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e35556 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35556
          have b8e37449 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) X1) ∨ x = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b8e561 x x x X0 X1 (M.op (M.op (M.op (M.op x x) x) x) (M.op (M.op (M.op x x) x) x))
               have i₂ := b8e35603 (M.op (M.op (M.op x x) x) x)
               grind)
            | exact superpose b8e35603 b8e561
            | exact resolve b8e561 b8e35603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e561 b8e35603
          have b8e38712 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            intro X1
            first
            | (have i₁ := b8e37449 (M.op x X1) X1
               have i₂ := b8e37449 x X1
               grind)
            | exact superpose b8e37449 b8e37449
            | exact resolve b8e37449 b8e37449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39108 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
            intro X1
            first
            | (have j0 := b8e38712 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38712
          have b8e40347 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e30 x
               have i₂ := b8e39108 (σ x)
               grind)
            | exact superpose b8e39108 b8e30
            | exact resolve b8e30 b8e39108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e42230 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e40347
               grind)
            | exact superpose b8e40347 b8e14
            | exact resolve b8e14 b8e40347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40347
          have b8e42309 : x = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e42230
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e42230
            | exact resolve b8e42230 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42230
          have b8e43602 : (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e37449 x x
               have i₂ := b8e42309
               grind)
            | exact superpose b8e42309 b8e37449
            | exact resolve b8e37449 b8e42309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37449
          have b8e43603 : (σ x) = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e43602
          have b8e44923 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e42309
               have i₂ := b8e43603
               grind)
            | exact superpose b8e43603 b8e42309
            | exact resolve b8e42309 b8e43603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42309 b8e43603
          have b8e45078 : x = (M.op x y) ∨ x = (σ x) := by grind
          clear b8e44923
          have b8e46195 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ x = (σ x) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 x y
               have i₂ := b8e45078
               grind)
            | exact superpose b8e45078 b8e32
            | exact resolve b8e32 b8e45078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53607 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ x = (σ x) ∨ x = (σ x) := by
            intro X1
            first
            | (have i₁ := b8e46195 (M.op x X1) X1
               have i₂ := b8e46195 x X1
               grind)
            | exact superpose b8e46195 b8e46195
            | exact resolve b8e46195 b8e46195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46195
          have b8e54084 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ x = (σ x) := by
            intro X1
            first
            | (have j0 := b8e53607 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53607
          have b8e55780 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ x) ∨ x = (σ x) := by
            intro X0
            first
            | (have i₁ := b8e54084 x
               have i₂ := b8e45078
               grind)
            | exact superpose b8e45078 b8e54084
            | exact resolve b8e54084 b8e45078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45078 b8e54084
          have b8e56147 : ∀ X0 : G, x = (M.op x X0) ∨ x = (σ x) := by
            intro X0
            first
            | (have j0 := b8e55780 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55780
          have b8e57215 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x ∨ x = (σ x) := by
            intro X0
            first
            | (have i₁ := b8e35 X0 x
               have i₂ := b8e56147 (M.op x x)
               grind)
            | exact superpose b8e56147 b8e35
            | exact resolve b8e35 b8e56147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e58937 : ∀ X0 : G, x = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ x = (σ x) := by
            intro X0
            first
            | (have i₁ := b8e501 X0 x x (M.op (M.op (M.op x x) x) (M.op (M.op x x) x))
               have i₂ := b8e57215 (M.op (M.op x x) x)
               grind)
            | exact superpose b8e57215 b8e501
            | exact resolve b8e501 b8e57215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e501 b8e57215
          have b8e74819 : x = (M.op (τ x) (τ x)) ∨ x = (σ x) ∨ x = (σ x) := by
            first
            | (have i₁ := b8e58937 x
               have i₂ := b8e56147 x
               grind)
            | exact superpose b8e56147 b8e58937
            | exact resolve b8e58937 b8e56147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58937
          have b8e74934 : x = (M.op (τ x) (τ x)) ∨ x = (σ x) := by grind
          clear b8e74819
          have b8e74947 : x = (τ (M.op x x)) ∨ x = (σ x) := by
            first
            | (have i₁ := b8e74934
               have i₂ := b8e124 x
               grind)
            | exact superpose b8e124 b8e74934
            | exact resolve b8e74934 b8e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124 b8e74934
          have b8e76288 : x = (τ x) ∨ x = (σ x) ∨ x = (σ x) := by
            first
            | (have i₁ := b8e74947
               have i₂ := b8e56147 x
               grind)
            | exact superpose b8e56147 b8e74947
            | exact resolve b8e74947 b8e56147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56147 b8e74947
          have b8e76354 : x = (τ x) ∨ x = (σ x) := by grind
          clear b8e76288
          have b8e77429 : x = (σ x) ∨ x = (σ x) := by
            first
            | (have i₁ := b8e15 x
               have i₂ := b8e76354
               grind)
            | exact superpose b8e76354 b8e15
            | exact resolve b8e15 b8e76354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76354
          have b8e77466 : x = (σ x) := by grind
          clear b8e77429
          have b8e78619 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e20
            | exact resolve b8e20 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e78624 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e39108 x
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e39108
            | exact resolve b8e39108 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39108
          have b8e100038 : x ≠ x ∨ x = (M.op x y) := by
            first
            | (have j0 := b8e78624 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78624
          have b8e100039 : x = (M.op x y) := by grind
          clear b8e100038
          have b8e102468 : (σ x) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e78619
               have i₂ := b8e100039
               grind)
            | exact superpose b8e100039 b8e78619
            | exact resolve b8e78619 b8e100039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78619
          have b8e102474 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x y
               have i₂ := b8e100039
               grind)
            | exact superpose b8e100039 b8e13
            | exact resolve b8e13 b8e100039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e102477 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 x y
               have i₂ := b8e100039
               grind)
            | exact superpose b8e100039 b8e32
            | exact resolve b8e32 b8e100039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e102582 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e102477 X0 X1
               have i₂ := b8e100039
               grind)
            | exact superpose b8e100039 b8e102477
            | exact resolve b8e102477 b8e100039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102477
          have b8e102585 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e102474 X0
               have i₂ := b8e100039
               grind)
            | exact superpose b8e100039 b8e102474
            | exact resolve b8e102474 b8e100039
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100039 b8e102474
          have b8e102586 : x ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e102468
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e102468
            | exact resolve b8e102468 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102468
          have b8e104157 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (τ (τ (M.op X6 X6))) (τ (τ X6))) = (M.op (M.op (σ (M.op (M.op X0 X1) X1)) (σ (M.op (M.op X2 X3) X3))) X5) := by
            intro X0 X1 X2 X3 X5 X6
            first
            | (have i₁ := b8e1338 X6 (M.op x X5) X5
               have i₂ := b8e581 X2 X3 x X5 X0 X1
               grind)
            | exact superpose b8e581 b8e1338
            | exact resolve b8e1338 b8e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1338
          have b8e104356 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op (M.op (σ (M.op (M.op X3 X4) X4)) (M.op (M.op X0 X1) X1)) X5) X6) X7) := by
            intro X0 X1 X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b8e846 (σ (M.op (M.op X3 X4) X4)) X5 X2 X6 X7
               have i₂ := b8e581 X3 X4 X0 X1 X3 X4
               grind)
            | exact superpose b8e581 b8e846
            | exact resolve b8e846 b8e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e104357 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op (M.op X4 (M.op X4 X4)) X5) X6) X7) = (M.op (σ (M.op (M.op X2 X3) X3)) (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b8e846 X4 X5 (σ (M.op (M.op X2 X3) X3)) X6 X7
               have i₂ := b8e581 X2 X3 X0 X1 X2 X3
               grind)
            | exact superpose b8e581 b8e846
            | exact resolve b8e846 b8e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e846
          have b8e104377 : ∀ X0 X1 X2 X3 X4 : G, (M.op (τ (τ (M.op X4 X4))) (τ (τ X4))) = (M.op (σ (M.op (M.op X2 X3) X3)) (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e1456 X4 (σ (M.op (M.op X2 X3) X3))
               have i₂ := b8e581 X2 X3 X0 X1 X2 X3
               grind)
            | exact superpose b8e581 b8e1456
            | exact resolve b8e1456 b8e581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e581 b8e1456
          have b8e104486 : ∀ X2 X3 X4 : G, (M.op (τ (τ (M.op X4 X4))) (τ (τ X4))) = (M.op (σ (M.op (M.op X2 X3) X3)) x) := by
            intro X2 X3 X4
            first
            | (have i₁ := b8e104377 x x X2 X3 X4
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104377
            | exact resolve b8e104377 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104377
          have b8e104506 : ∀ X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op (M.op X4 (M.op X4 X4)) X5) X6) X7) = (M.op (σ (M.op (M.op X2 X3) X3)) x) := by
            intro X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b8e104357 x x X2 X3 X4 X5 X6 X7
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104357
            | exact resolve b8e104357 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104357
          have b8e104507 : ∀ X2 X3 X4 X5 X6 X7 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op (M.op (σ (M.op (M.op X3 X4) X4)) x) X5) X6) X7) := by
            intro X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b8e104356 x x X2 X3 X4 X5 X6 X7
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104356
            | exact resolve b8e104356 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104356
          have b8e104660 : ∀ X0 X1 X5 X6 : G, (M.op (τ (τ (M.op X6 X6))) (τ (τ X6))) = (M.op (M.op (σ (M.op (M.op X0 X1) X1)) (σ x)) X5) := by
            intro X0 X1 X5 X6
            first
            | (have i₁ := b8e104157 X0 X1 x x X5 X6
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104157
            | exact resolve b8e104157 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104157
          have b8e105132 : ∀ X4 : G, (M.op (τ (τ (M.op X4 X4))) (τ (τ X4))) = (M.op (σ x) x) := by
            intro X4
            first
            | (have i₁ := b8e104486 x x X4
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104486
            | exact resolve b8e104486 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104486
          have b8e105152 : ∀ X4 X5 X6 X7 : G, (M.op (σ x) x) = (M.op (M.op (M.op (M.op X4 (M.op X4 X4)) X5) X6) X7) := by
            intro X4 X5 X6 X7
            first
            | (have i₁ := b8e104506 x x X4 X5 X6 X7
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104506
            | exact resolve b8e104506 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104506
          have b8e105153 : ∀ X2 X5 X6 X7 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op (M.op (σ x) x) X5) X6) X7) := by
            intro X2 X5 X6 X7
            first
            | (have i₁ := b8e104507 X2 x x X5 X6 X7
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e104507
            | exact resolve b8e104507 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104507
          have b8e105306 : ∀ X0 X1 X5 X6 : G, (M.op (τ (τ (M.op X6 X6))) (τ (τ X6))) = (M.op (M.op (σ (M.op (M.op X0 X1) X1)) x) X5) := by
            intro X0 X1 X5 X6
            first
            | (have i₁ := b8e104660 X0 X1 X5 X6
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e104660
            | exact resolve b8e104660 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104660
          have b8e105778 : ∀ X4 : G, (M.op (τ (τ (M.op X4 X4))) (τ (τ X4))) = (M.op x x) := by
            intro X4
            first
            | (have i₁ := b8e105132 X4
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e105132
            | exact resolve b8e105132 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105132
          have b8e105798 : ∀ X5 X6 X7 : G, (M.op (σ x) x) = (M.op (M.op (M.op x X5) X6) X7) := by
            intro X5 X6 X7
            first
            | (have i₁ := b8e105152 x X5 X6 X7
               have i₂ := b8e102585 x
               grind)
            | exact superpose b8e102585 b8e105152
            | exact resolve b8e105152 b8e102585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105152
          have b8e105799 : ∀ X2 X5 X6 X7 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op (M.op x x) X5) X6) X7) := by
            intro X2 X5 X6 X7
            first
            | (have i₁ := b8e105153 X2 X5 X6 X7
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e105153
            | exact resolve b8e105153 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105153
          have b8e105951 : ∀ X5 X6 : G, (M.op (τ (τ (M.op X6 X6))) (τ (τ X6))) = (M.op (M.op (σ x) x) X5) := by
            intro X5 X6
            first
            | (have i₁ := b8e105306 x x X5 X6
               have i₂ := b8e102582 x x
               grind)
            | exact superpose b8e102582 b8e105306
            | exact resolve b8e105306 b8e102582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102582 b8e105306
          have b8e106360 : ∀ X5 X6 X7 : G, (M.op x x) = (M.op (M.op (M.op x X5) X6) X7) := by
            intro X5 X6 X7
            first
            | (have i₁ := b8e105798 X5 X6 X7
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e105798
            | exact resolve b8e105798 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105798
          have b8e106361 : ∀ X5 X6 X7 : G, x = (M.op (M.op (M.op (M.op x x) X5) X6) X7) := by
            intro X5 X6 X7
            first
            | (have i₁ := b8e105799 x X5 X6 X7
               have i₂ := b8e102585 x
               grind)
            | exact superpose b8e102585 b8e105799
            | exact resolve b8e105799 b8e102585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102585 b8e105799
          have b8e106461 : ∀ X5 X6 : G, (M.op (τ (τ (M.op X6 X6))) (τ (τ X6))) = (M.op (M.op x x) X5) := by
            intro X5 X6
            first
            | (have i₁ := b8e105951 X5 X6
               have i₂ := b8e77466
               grind)
            | exact superpose b8e77466 b8e105951
            | exact resolve b8e105951 b8e77466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77466 b8e105951
          have b8e106825 : ∀ X7 : G, x = (M.op (M.op x x) X7) := by
            intro X7
            first
            | (have i₁ := b8e106361 x x X7
               have i₂ := b8e106360 x x x
               grind)
            | exact superpose b8e106360 b8e106361
            | exact resolve b8e106361 b8e106360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106360 b8e106361
          have b8e106911 : ∀ X5 : G, (M.op x x) = (M.op (M.op x x) X5) := by
            intro X5
            first
            | (have i₁ := b8e106461 X5 x
               have i₂ := b8e105778 x
               grind)
            | exact superpose b8e105778 b8e106461
            | exact resolve b8e106461 b8e105778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105778 b8e106461
          have b8e107243 : x = (M.op x x) := by
            first
            | (have i₁ := b8e106911 x
               have i₂ := b8e106825 x
               grind)
            | exact superpose b8e106825 b8e106911
            | exact resolve b8e106911 b8e106825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106911
          have b8e114475 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e106825 X0
               have i₂ := b8e107243
               grind)
            | exact superpose b8e107243 b8e106825
            | exact resolve b8e106825 b8e107243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106825 b8e107243
          have b8e116771 : x ≠ x := by
            first
            | (have i₁ := b8e102586
               have i₂ := b8e114475 (σ y)
               grind)
            | exact superpose b8e114475 b8e102586
            | (have r₁ := b8e102586
               have r₂ := b8e114475 (σ y)
               grind)
            | exact resolve b8e102586 b8e114475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102586 b8e114475
          have b8e117097 : False := by grind
          exact b8e117097

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyy_x_pxy_Equation4400 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4400 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ x) ≠ (σ x) := by
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
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ x) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : x = (M.op x x) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e36 y
             grind)
          | exact superpose b1e36 b1e20
          | exact resolve b1e20 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e49 : ∀ X0 : G, x ≠ (M.op x x) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e36 X0
             grind)
          | (have i₁ := b1e15 x x
             have i₂ := b1e36 X0
             grind)
          | exact superpose b1e36 b1e15
          | (have j0 := b1e15 x x
             grind)
          | exact resolve b1e15 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e49 X0
             grind)
          | (have r₁ := b1e49 X0
             have r₂ := b1e42
             grind)
          | exact resolve b1e49 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e57 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e36
          | exact resolve b1e36 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e42
        have b1e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k x (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e87 X0 X1
             have i₂ := b1e51 (σ X0)
             grind)
          | exact superpose b1e51 b1e87
          | (have j0 := b1e87 X0 X1
             grind)
          | exact resolve b1e87 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e126 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e21
          | exact resolve b1e21 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e224 : (σ y) = (k x (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e51 (σ x)
             grind)
          | exact superpose b1e51 b1e22
          | exact resolve b1e22 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e310 : (σ x) ≠ (k x (σ y)) := by
          first
          | (have i₁ := b1e126 (σ y)
             have i₂ := b1e51 (σ y)
             grind)
          | exact superpose b1e51 b1e126
          | exact resolve b1e126 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e1051 : (σ y) = (σ (k x x)) ∨ (σ x) = (k x (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e96 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e96
          | (have j0 := b1e96 x x
             grind)
          | exact resolve b1e96 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e96
        have b1e1099 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (k x (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1051
             have i₂ := b1e51 x
             grind)
          | exact superpose b1e51 b1e1051
          | exact resolve b1e1051 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e1051
        have b1e1114 : (σ x) = (σ y) ∨ (σ x) = (k x (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1099
             have i₂ := b1e57 x
             grind)
          | exact superpose b1e57 b1e1099
          | exact resolve b1e1099 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e1099
        have b1e1115 : (σ x) = (σ y) ∨ (σ x) = (k x (σ x)) := by grind
        clear b1e1114
        have b1e1120 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1115
             have i₂ := b1e224
             grind)
          | exact superpose b1e224 b1e1115
          | exact resolve b1e1115 b1e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1115
        have b1e1121 : (σ x) = (σ y) := by grind
        clear b1e1120
        have b1e1128 : (σ x) ≠ (k x (σ x)) := by
          first
          | (have i₁ := b1e310
             have i₂ := b1e1121
             grind)
          | exact superpose b1e1121 b1e310
          | exact resolve b1e310 b1e1121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e310
        have b1e1144 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e1128
             have i₂ := b1e224
             grind)
          | exact superpose b1e224 b1e1128
          | exact resolve b1e1128 b1e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e224 b1e1128
        have b1e1147 : False := by grind
        exact b1e1147
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X3
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
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
        have b2e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X0 X1) X2)
             have i₂ := b2e12 (M.op X0 X1) X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : x = (M.op x x) := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e33 y
             grind)
          | exact superpose b2e33 b2e20
          | exact resolve b2e20 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : ∀ X0 : G, x ≠ (M.op x x) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e33 X0
             grind)
          | (have i₁ := b2e15 x x
             have i₂ := b2e33 X0
             grind)
          | exact superpose b2e33 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X0 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op X0 X1)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e46 X0 X1 X2
             have i₂ := b2e12 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e12 b2e46
          | (have j0 := b2e46 X0 X1 X2
             grind)
          | exact resolve b2e46 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e50 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e45 X0
             grind)
          | (have r₁ := b2e45 X0
             have r₂ := b2e41
             grind)
          | exact resolve b2e45 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e52 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e33 X0
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e33
          | exact resolve b2e33 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e41
        have b2e80 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X0 X2
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e162 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2
          grind
        have b2e163 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e162 X0 X1 X2
             have i₂ := b2e12 X0 X1 (M.op (M.op X0 X1) X2)
             grind)
          | exact superpose b2e12 b2e162
          | (have j0 := b2e162 X0 X1 X2
             grind)
          | exact resolve b2e162 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e162
        have b2e176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k x (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 X0 X1 (M.op X0 X1) X2
             have i₂ := b2e50 (M.op X0 X1)
             grind)
          | exact superpose b2e50 b2e31
          | exact resolve b2e31 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e177 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k x (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op X0 X1)
             have i₂ := b2e50 (M.op X0 X1)
             grind)
          | exact superpose b2e50 b2e12
          | exact resolve b2e12 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e228 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X3 X3) = (k (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 (M.op (M.op X0 X1) X2) X3
             have i₂ := b2e36 X0 X1 X2 X3
             grind)
          | exact superpose b2e36 b2e15
          | (have j0 := b2e15 (M.op (M.op X0 X1) X2) X3
             grind)
          | exact resolve b2e15 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e230 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (k x (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e50 (M.op (M.op X0 X1) X2)
             have i₂ := b2e36 X0 X1 X2 (M.op (M.op X0 X1) X2)
             grind)
          | exact superpose b2e36 b2e50
          | exact resolve b2e50 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e234 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (k (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b2e228 X0 X1 X2 X3
             grind)
          | (have r₁ := b2e228 X0 X1 X2 X3
             have r₂ := b2e12 X0 X1 X2
             grind)
          | exact resolve b2e228 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228
        have b2e535 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op (k x X0) X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e234 X0 X0 X2 X1
             have i₂ := b2e50 X0
             grind)
          | exact superpose b2e50 b2e234
          | exact resolve b2e234 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234
        have b2e611 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e49 X0 X0 X2
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e49 X0 X1 X2
             have i₂ := b2e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b2e17 b2e49
          | (have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e49 X1 X1 (M.op X1 X1)
             have r₂ := b2e17 (M.op X1 X1) X1
             grind)
          | (have r₁ := b2e49 (M.op X0 X0) X1 X2
             have r₂ := b2e17 X0 (M.op (M.op (M.op X0 X0) X1) X2)
             grind)
          | exact resolve b2e49 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e620 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e49 X0 X1 x
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e49
          | (have j0 := b2e49 X0 X1 x
             grind)
          | exact resolve b2e49 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e630 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e611 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e611
        have b2e826 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X0 X2
             have i₂ := b2e80 X0 X0 X1
             grind)
          | (have i₁ := b2e17 X2 X1
             have i₂ := b2e80 X2 X1 X2
             grind)
          | exact superpose b2e80 b2e17
          | (have j0 := b2e17 X0 X0
             have j1 := b2e80 X2 X0 X2
             grind)
          | exact resolve b2e17 b2e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80
        have b2e894 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e826 X0 X0 X0
             have j1 := b2e630 X0 X0 X2
             grind)
          | (have r₁ := b2e826 X0 X2 X1
             have r₂ := b2e630 X0 X1 X2
             grind)
          | (have r₁ := b2e826 X0 X1 (M.op X0 X2)
             have r₂ := b2e630 X0 (M.op X0 X1) X2
             grind)
          | (have r₁ := b2e826 X0 X1 X2
             have r₂ := b2e630 X0 (k X0 X2) X2
             grind)
          | exact resolve b2e826 b2e630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e630 b2e826
        have b2e909 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e894 X0 X1 X2
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e894 X0 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e894 X0 X1 (M.op (M.op X0 X1) X1)
             have r₂ := b2e15 (M.op X0 X1) X1
             grind)
          | (have r₁ := b2e894 X1 X1 X2
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e894 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e894
        have b2e17539 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e909 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e909
        have b2e17540 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e17539 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17539
        have b2e17907 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e620 X0 x
             have i₂ := b2e17540 X0 x
             grind)
          | exact superpose b2e17540 b2e620
          | (have j1 := b2e17540 X0 x
             grind)
          | (have r₁ := b2e620 X0 x
             have r₂ := b2e17540 X0 (M.op X0 x)
             grind)
          | exact resolve b2e620 b2e17540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e620
        have b2e18046 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e17907 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17907
        have b2e18093 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e18046 X0
             have j1 := b2e17540 X0 x
             grind)
          | (have r₁ := b2e18046 x
             have r₂ := b2e17540 x x
             grind)
          | exact resolve b2e18046 b2e17540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17540 b2e18046
        have b2e18745 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e18093 (σ X0)
             grind)
          | exact superpose b2e18093 b2e18
          | exact resolve b2e18 b2e18093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e18779 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18745 X0
             have i₂ := b2e18093 X0
             grind)
          | exact superpose b2e18093 b2e18745
          | exact resolve b2e18745 b2e18093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18093 b2e18745
        have b2e18799 : ∀ X0 : G, (k x (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18779 X0
             have i₂ := b2e50 (σ X0)
             grind)
          | exact superpose b2e50 b2e18779
          | exact resolve b2e18779 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18779
        have b2e28821 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op (σ (M.op X0 X0)) X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e535 (σ X0) X1 X2
             have i₂ := b2e18799 X0
             grind)
          | exact superpose b2e18799 b2e535
          | exact resolve b2e535 b2e18799
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e535
        have b2e115761 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (σ x) X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e28821 x X0 X1
             have i₂ := b2e52 x
             grind)
          | exact superpose b2e52 b2e28821
          | exact resolve b2e28821 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28821
        have b2e119993 : ∀ X0 X1 : G, (k x X1) = (k (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e50 X1
             have i₂ := b2e115761 X1 X0
             grind)
          | exact superpose b2e115761 b2e50
          | exact resolve b2e50 b2e115761
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115761
        have b2e131399 : ∀ X0 X1 : G, (M.op (σ x) X0) = (k x (M.op (M.op (σ x) X0) X1)) ∨ (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e163 (σ x) X0 X1
             have i₂ := b2e119993 X0 (M.op (M.op (σ x) X0) X1)
             grind)
          | exact superpose b2e119993 b2e163
          | (have j0 := b2e163 (σ x) X0 x
             grind)
          | exact resolve b2e163 b2e119993
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163 b2e119993
        have b2e131469 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e131399 X0 x
             have i₂ := b2e230 (σ x) X0 x
             grind)
          | exact superpose b2e230 b2e131399
          | (have j0 := b2e131399 X0 x
             grind)
          | exact resolve b2e131399 b2e230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e230 b2e131399
        have b2e131470 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have j0 := b2e131469 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131469
        have b2e131519 : ∀ X0 : G, (M.op (σ x) X0) = (k x (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e131470 X0
             have i₂ := b2e177 (σ x) X0
             grind)
          | exact superpose b2e177 b2e131470
          | exact resolve b2e131470 b2e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177 b2e131470
        have b2e138533 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e176 (σ x) X0 X1
             have i₂ := b2e131519 X0
             grind)
          | exact superpose b2e131519 b2e176
          | exact resolve b2e176 b2e131519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e176 b2e131519
        have b2e138825 : ∀ X0 : G, (k x (σ x)) = (M.op (k x (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b2e138533 (σ x) x
             have i₂ := b2e50 (σ x)
             grind)
          | exact superpose b2e50 b2e138533
          | exact resolve b2e138533 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e138533
        have b2e139362 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) X0) := by
          intro X0
          first
          | (have i₁ := b2e138825 X0
             have i₂ := b2e18799 x
             grind)
          | exact superpose b2e18799 b2e138825
          | exact resolve b2e138825 b2e18799
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18799 b2e138825
        have b2e139422 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e139362 X0
             have i₂ := b2e52 x
             grind)
          | exact superpose b2e52 b2e139362
          | exact resolve b2e139362 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e139362
        have b2e139844 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e139422 (σ y)
             grind)
          | exact superpose b2e139422 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e139422 (σ y)
             grind)
          | exact resolve b2e21 b2e139422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139422
        have b2e140022 : False := by grind
        exact b2e140022
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e31 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e91 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e31 (σ y)
             grind)
          | exact superpose b3e31 b3e22
          | exact resolve b3e22 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e100 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e91
             grind)
          | exact superpose b3e91 b3e15
          | (have r₁ := b3e15 (σ x) (σ x)
             have r₂ := b3e91
             grind)
          | exact resolve b3e15 b3e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e104 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b3e100
        have b3e105 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e104
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e104
          | exact resolve b3e104 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104
        have b3e179 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e105
             grind)
          | exact superpose b3e105 b3e13
          | exact resolve b3e13 b3e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e181 : x = (k x x) := by
          first
          | (have i₁ := b3e179
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e179
          | exact resolve b3e179 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e179
        have b3e254 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e181
             grind)
          | exact superpose b3e181 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e181
        have b3e255 : x = (M.op x x) := by grind
        clear b3e254
        have b3e320 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e255
             grind)
          | exact superpose b3e255 b3e21
          | exact resolve b3e21 b3e255
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e452 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e320
             grind)
          | exact superpose b3e320 b3e20
          | exact resolve b3e20 b3e320
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320
        have b3e463 : False := by grind
        exact b3e463
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e29 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 X2 (k (τ X0) X1)
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e19
            | exact resolve b4e19 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e13 x x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 (M.op (M.op X0 X1) X2)
               have i₂ := b4e13 (M.op X0 X1) X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op y (M.op x y)) := by
            intro X1
            first
            | (have i₁ := b4e13 y x x
               have i₂ := b4e37 x
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) := by
            intro X1
            first
            | (have i₁ := b4e40 X1
               have i₂ := b4e37 (M.op x y)
               grind)
            | exact superpose b4e37 b4e40
            | exact resolve b4e40 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e42 : (M.op x y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e41 x
               have i₂ := b4e13 x y x
               grind)
            | exact superpose b4e13 b4e41
            | exact resolve b4e41 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (k (M.op X0 X1) X2) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 (M.op X0 X1) X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X0 X1) X2
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e88 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X1
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e36
            | exact resolve b4e36 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e20
            | exact resolve b4e20 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e218 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X3 X3) = (k (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16 (M.op (M.op X0 X1) X2) X3
               have i₂ := b4e38 X0 X1 X2 X3
               grind)
            | exact superpose b4e38 b4e16
            | (have j0 := b4e16 (M.op (M.op X0 X1) X2) X3
               grind)
            | exact resolve b4e16 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e223 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (k (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e218 X0 X1 X2 X3
               grind)
            | (have r₁ := b4e218 X0 X1 X2 X3
               have r₂ := b4e13 X0 X1 X2
               grind)
            | exact resolve b4e218 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e218
          have b4e511 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b4e44 x y X0
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e44
            | (have j0 := b4e44 x y X0
               grind)
            | (have r₁ := b4e44 x y x
               have r₂ := b4e42
               grind)
            | exact resolve b4e44 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e513 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) X0) := by
            intro X0
            first
            | (have j0 := b4e511 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e511
          have b4e544 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op x y) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e32 X0 X1 (M.op X0 X1) X2
               have i₂ := b4e513 (M.op X0 X1)
               grind)
            | exact superpose b4e513 b4e32
            | exact resolve b4e32 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e545 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op x y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (M.op X0 X1)
               have i₂ := b4e513 (M.op X0 X1)
               grind)
            | exact superpose b4e513 b4e13
            | exact resolve b4e13 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e551 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e31 (M.op x y) X0
               have i₂ := b4e513 (σ X0)
               grind)
            | exact superpose b4e513 b4e31
            | exact resolve b4e31 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e552 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e27 X0 (M.op x y)
               have i₂ := b4e513 (τ X0)
               grind)
            | exact superpose b4e513 b4e27
            | exact resolve b4e27 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e909 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op (k (M.op x y) X0) X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e223 X0 X0 X2 X1
               have i₂ := b4e513 X0
               grind)
            | exact superpose b4e513 b4e223
            | exact resolve b4e223 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223
          have b4e1398 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e66 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e1400 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e1398 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1398
          have b4e4864 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k (τ (M.op x y)) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e29 (M.op x y) X0 X1
               have i₂ := b4e513 (σ X0)
               grind)
            | exact superpose b4e513 b4e29
            | exact resolve b4e29 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5256 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (k (τ (M.op x y)) y) := by
            intro X0
            first
            | (have i₁ := b4e551 y
               have i₂ := b4e88 (σ y) X0
               grind)
            | (have i₁ := b4e551 y
               have i₂ := b4e88 X0 (σ y)
               grind)
            | exact superpose b4e88 b4e551
            | exact resolve b4e551 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88 b4e551
          have b4e7253 : (σ (M.op x y)) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e1400 (M.op x y)
               have i₂ := b4e545 x y
               grind)
            | exact superpose b4e545 b4e1400
            | (have j0 := b4e1400 (M.op x y)
               grind)
            | exact resolve b4e1400 b4e545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545 b4e1400
          have b4e7294 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e7253
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e7253
            | exact resolve b4e7253 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e7253
          have b4e7295 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b4e7294
          have b4e7315 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e7295
               have i₂ := b4e513 (σ (M.op x y))
               grind)
            | exact superpose b4e513 b4e7295
            | exact resolve b4e7295 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7295
          have b4e7394 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op x y)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e552 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e552
            | exact resolve b4e552 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7474 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e7394 X0
               have i₂ := b4e19 (M.op x y) X0
               grind)
            | exact superpose b4e19 b4e7394
            | exact resolve b4e7394 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7394
          have b4e7521 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (σ (M.op (M.op X0 X1) (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e7474 (M.op X0 X1)
               have i₂ := b4e544 X0 X1 X2
               grind)
            | exact superpose b4e544 b4e7474
            | exact resolve b4e7474 b4e544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e544
          have b4e7554 : ∀ X0 X1 : G, (k (σ X1) (σ (M.op X0 X0))) = (σ (k X1 (k (M.op x y) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 (k (M.op x y) X0)
               have i₂ := b4e7474 X0
               grind)
            | exact superpose b4e7474 b4e19
            | exact resolve b4e19 b4e7474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7584 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (σ (k X1 (k (M.op x y) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e7554 X0 X1
               have i₂ := b4e19 X1 (M.op X0 X0)
               grind)
            | exact superpose b4e19 b4e7554
            | exact resolve b4e7554 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7554
          have b4e7611 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (σ (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e7521 X0 X1 X2
               have i₂ := b4e13 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e13 b4e7521
            | exact resolve b4e7521 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7521
          have b4e16597 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (σ (M.op x y)) X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e909 (σ (M.op x y)) X0 X1
               have i₂ := b4e7315
               grind)
            | exact superpose b4e7315 b4e909
            | exact resolve b4e909 b4e7315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e909
          have b4e17283 : ∀ X0 : G, (M.op X0 X0) = (k (k (M.op x y) (σ (M.op x y))) X0) := by
            intro X0
            first
            | (have i₁ := b4e16597 X0 (σ (M.op x y))
               have i₂ := b4e513 (σ (M.op x y))
               grind)
            | exact superpose b4e513 b4e16597
            | exact resolve b4e16597 b4e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e513 b4e16597
          have b4e17474 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e17283 X0
               have i₂ := b4e7315
               grind)
            | exact superpose b4e7315 b4e17283
            | exact resolve b4e17283 b4e7315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7315 b4e17283
          have b4e17767 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e552 X0
               have i₂ := b4e17474 X0
               grind)
            | exact superpose b4e17474 b4e552
            | exact resolve b4e552 b4e17474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e552
          have b4e17783 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k (τ (σ (M.op x y))) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e29 (σ (M.op x y)) X0 X1
               have i₂ := b4e17474 (σ X0)
               grind)
            | exact superpose b4e17474 b4e29
            | exact resolve b4e29 b4e17474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e17474
          have b4e17794 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k (M.op x y) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e17783 X0 X1
               have i₂ := b4e14 (M.op x y)
               grind)
            | exact superpose b4e14 b4e17783
            | exact resolve b4e17783 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17783
          have b4e18105 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (σ (M.op (k (τ (M.op x y)) y) (k (τ (M.op x y)) y))) := by
            intro X0
            first
            | (have i₁ := b4e17767 (M.op (σ y) X0)
               have i₂ := b4e5256 X0
               grind)
            | exact superpose b4e5256 b4e17767
            | exact resolve b4e17767 b4e5256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5256 b4e17767
          have b4e18169 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (σ (k (M.op x y) (k (τ (M.op x y)) y))) := by
            intro X0
            first
            | (have i₁ := b4e18105 X0
               have i₂ := b4e7474 (k (τ (M.op x y)) y)
               grind)
            | exact superpose b4e7474 b4e18105
            | exact resolve b4e18105 b4e7474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18105
          have b4e18185 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e18169 X0
               have i₂ := b4e4864 y (M.op x y)
               grind)
            | exact superpose b4e4864 b4e18169
            | exact resolve b4e18169 b4e4864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4864 b4e18169
          have b4e18198 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (σ (k (M.op x y) (k (M.op x y) y))) := by
            intro X0
            first
            | (have i₁ := b4e18185 X0
               have i₂ := b4e17794 y (M.op x y)
               grind)
            | exact superpose b4e17794 b4e18185
            | exact resolve b4e18185 b4e17794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17794 b4e18185
          have b4e18207 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (σ (k (M.op x y) (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e18198 X0
               have i₂ := b4e7584 y (M.op x y)
               grind)
            | exact superpose b4e7584 b4e18198
            | exact resolve b4e18198 b4e7584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7584 b4e18198
          have b4e18210 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (σ (M.op (M.op y y) (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e18207 X0
               have i₂ := b4e7474 (M.op y y)
               grind)
            | exact superpose b4e7474 b4e18207
            | exact resolve b4e18207 b4e7474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7474 b4e18207
          have b4e18212 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (σ (M.op y (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b4e18210 X0
               have i₂ := b4e7611 y y (M.op y y)
               grind)
            | exact superpose b4e7611 b4e18210
            | exact resolve b4e18210 b4e7611
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7611 b4e18210
          have b4e18214 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e18212 X0
               have i₂ := b4e37 (M.op y y)
               grind)
            | exact superpose b4e37 b4e18212
            | exact resolve b4e18212 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e18212
          have b4e18216 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e18214 X0
               have i₂ := b4e13 (σ y) X0 (M.op (σ y) X0)
               grind)
            | exact superpose b4e13 b4e18214
            | exact resolve b4e18214 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18214
          have b4e18218 : False := by grind
          exact b4e18218
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b5e53 : x = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e892 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e893 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e892
               have r₂ := b5e23
               grind)
            | exact resolve b5e892 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e892
          have b5e894 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e893
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e893
            | exact resolve b5e893 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e893
          have b5e895 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e894
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e894
            | exact resolve b5e894 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e894
          have b5e896 : False := by grind
          exact b5e896
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e29 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ y) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e29 (σ y)
             grind)
          | exact superpose b6e29 b6e22
          | exact resolve b6e22 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e84 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e62
             grind)
          | exact superpose b6e62 b6e15
          | (have r₁ := b6e15 (σ x) (σ x)
             have r₂ := b6e62
             grind)
          | exact resolve b6e15 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e88 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b6e84
        have b6e89 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e88
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e88
          | exact resolve b6e88 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e149 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e89
             grind)
          | exact superpose b6e89 b6e13
          | exact resolve b6e13 b6e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e151 : x = (k x x) := by
          first
          | (have i₁ := b6e149
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e149
          | exact resolve b6e149 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e213 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e151
             grind)
          | exact superpose b6e151 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e151
        have b6e214 : x = (M.op x x) := by grind
        clear b6e213
        have b6e271 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e12 x x x
             have i₂ := b6e214
             grind)
          | exact superpose b6e214 b6e12
          | exact resolve b6e12 b6e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e274 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e271 X0
             have i₂ := b6e214
             grind)
          | exact superpose b6e214 b6e271
          | exact resolve b6e271 b6e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e214 b6e271
        have b6e399 : x ≠ x := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e274 y
             grind)
          | exact superpose b6e274 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e274 y
             grind)
          | exact resolve b6e20 b6e274
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e274
        have b6e410 : False := by grind
        exact b6e410
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e64 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e71 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e23
               grind)
            | exact resolve b7e64 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e72 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e71
            | exact resolve b7e71 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e75 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e14
            | exact resolve b7e14 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e76 : x = (k x y) := by
            first
            | (have i₁ := b7e75
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e75
            | exact resolve b7e75 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e98 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e99 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e98
          have b7e101 : y = (M.op x x) := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e21
               grind)
            | exact resolve b7e99 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e103 : False := by grind
          exact b7e103
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e87 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e955 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e87 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87
          have b8e956 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e955
               have r₂ := b8e23
               grind)
            | exact resolve b8e955 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e955
          have b8e957 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e956
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e956
            | exact resolve b8e956 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e956
          have b8e960 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e957
               grind)
            | exact superpose b8e957 b8e20
            | exact resolve b8e20 b8e957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e957
          have b8e1199 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e960
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e960
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e960 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e960
          have b8e1200 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e1199
          have b8e1205 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1200
               have r₂ := b8e22
               grind)
            | exact resolve b8e1200 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1200
          have b8e1210 : False := by grind
          exact b8e1210

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxx_pxy_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ y) ≠ (σ y) := by
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
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : x = y := by
          first
          | (have i₁ := b1e27
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e27
          | exact resolve b1e27 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e29 : y = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e20
          | exact resolve b1e20 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e29
             grind)
          | exact superpose b1e29 b1e15
          | (have r₁ := b1e15 y y
             have r₂ := b1e29
             grind)
          | exact resolve b1e15 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e66 : y = (k y y) := by grind
        clear b1e62
        have b1e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e459 : (M.op (σ y) (σ y)) = (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e73 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e73
          | (have j0 := b1e73 y
             grind)
          | exact resolve b1e73 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e476 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
          first
          | (have r₁ := b1e459
             have r₂ := b1e24
             grind)
          | exact resolve b1e459 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e459
        have b1e478 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e476
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e476
          | exact resolve b1e476 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e476
        have b1e480 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e478
             have i₂ := b1e66
             grind)
          | exact superpose b1e66 b1e478
          | exact resolve b1e478 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e478
        have b1e481 : False := by grind
        exact b1e481
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e34 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e34 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e34
          | exact resolve b2e34 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : y = (M.op y x) := by
          first
          | (have i₁ := b2e38
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e38
          | exact resolve b2e38 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e48 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b2e52 : (k x y) = (M.op x x) := by grind
        clear b2e48
        have b2e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e965 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e62 x y
             grind)
          | exact superpose b2e62 b2e21
          | (have j1 := b2e62 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e62 y x
             grind)
          | exact resolve b2e21 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e985 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e62 y x
             grind)
          | exact superpose b2e62 b2e21
          | (have j1 := b2e62 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e62 y x
             grind)
          | exact resolve b2e21 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e1007 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
        clear b2e985
        have b2e1012 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e1007
             have r₂ := b2e22
             grind)
          | exact resolve b2e1007 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1007
        have b2e1015 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e965
             have r₂ := b2e22
             grind)
          | exact resolve b2e965 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e965
        have b2e1020 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1012
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e1012
          | exact resolve b2e1012 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e1012
        have b2e3233 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e1015
             have i₂ := b2e17 y x
             grind)
          | exact superpose b2e17 b2e1015
          | (have j1 := b2e17 (σ x) (M.op (σ y) (σ x))
             grind)
          | (have r₁ := b2e1015
             have r₂ := b2e17 (σ y) (σ (k y x))
             grind)
          | (have r₁ := b2e1015
             have r₂ := b2e17 (σ (k y x)) (σ y)
             grind)
          | exact resolve b2e1015 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1015
        have b2e3234 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e3233
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3233
          | exact resolve b2e3233 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3233
        have b2e3235 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by grind
        clear b2e3234
        have b2e3236 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e3235
             have i₂ := b2e1020
             grind)
          | exact superpose b2e1020 b2e3235
          | exact resolve b2e3235 b2e1020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1020 b2e3235
        have b2e3237 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
          first
          | (have i₁ := b2e3236
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e3236
          | exact resolve b2e3236 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3236
        have b2e3238 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
        clear b2e3237
        have b2e3493 : (M.op x x) = (τ (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e13 (M.op x x)
             have i₂ := b2e3238
             grind)
          | exact superpose b2e3238 b2e13
          | exact resolve b2e13 b2e3238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3238
        have b2e3523 : x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e3493
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e3493
          | exact resolve b2e3493 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3493
        have b2e3797 : (M.op y x) = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e34 x
             have i₂ := b2e3523
             grind)
          | exact superpose b2e3523 b2e34
          | exact resolve b2e34 b2e3523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e3838 : y = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e3797
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e3797
          | exact resolve b2e3797 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e3797
        have b2e4414 : x = y ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e3523
             have i₂ := b2e3838
             grind)
          | exact superpose b2e3838 b2e3523
          | exact resolve b2e3523 b2e3838
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3523 b2e3838
        have b2e4453 : x = y := by grind
        clear b2e4414
        have b2e4510 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e4453
             grind)
          | exact superpose b2e4453 b2e22
          | exact resolve b2e22 b2e4453
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4453
        have b2e4524 : False := by grind
        exact b2e4524
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : (σ y) ≠ (σ (M.op y y)) := by grind
        have b3e52 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
        have b3e55 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e52
        have b3e56 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e55
          | exact resolve b3e55 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e67 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b3e56
        have b3e68 : y = (M.op y y) := by
          first
          | (have r₁ := b3e67
             have r₂ := b3e27
             grind)
          | exact resolve b3e67 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e67
        have b3e71 : False := by grind
        exact b3e71
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x y) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e357 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e61
          have b4e373 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e357
          have b4e376 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e373
          have b4e377 : y = (M.op y y) := by grind
          clear b4e376
          have b4e378 : False := by grind
          exact b4e378
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e27 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e27
          | exact resolve b6e27 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e40 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e43 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e40
        have b6e44 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e43
          | exact resolve b6e43 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e59 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e35 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e35
          | exact resolve b6e35 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b6e35 (σ x)
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e35
          | exact resolve b6e35 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e289 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
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
        have b6e301 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e289
             have r₂ := b6e21
             grind)
          | exact resolve b6e289 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e289
        have b6e302 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
          first
          | (have r₁ := b6e301
             have r₂ := b6e20
             grind)
          | exact resolve b6e301 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e301
        have b6e1017 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e68 x y
             grind)
          | exact superpose b6e68 b6e22
          | (have j1 := b6e68 x y
             grind)
          | exact resolve b6e22 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e1076 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1017
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e1017
          | exact resolve b6e1017 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e1017
        have b6e1077 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1076
        have b6e1150 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e1077
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e1077
          | (have j1 := b6e17 (σ (M.op x y)) (σ y)
             grind)
          | exact resolve b6e1077 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1077
        have b6e1166 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e1150
             have r₂ := b6e24
             grind)
          | exact resolve b6e1150 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e1150
        have b6e1167 : x = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1166
             have r₂ := b6e21
             grind)
          | exact resolve b6e1166 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1166
        have b6e1299 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e302
             have i₂ := b6e1167
             grind)
          | exact superpose b6e1167 b6e302
          | exact resolve b6e302 b6e1167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e302
        have b6e1317 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1299
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e1299
          | exact resolve b6e1299 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e1299
        have b6e1686 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e1317
             grind)
          | exact superpose b6e1317 b6e13
          | exact resolve b6e13 b6e1317
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1317
        have b6e1712 : y = (k x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1686
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1686
          | exact resolve b6e1686 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1686
        have b6e1767 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e1712
             grind)
          | exact superpose b6e1712 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e1712
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1712
        have b6e1768 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1767
             have r₂ := b6e21
             grind)
          | exact resolve b6e1767 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1767
        have b6e1770 : y = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1768
             have r₂ := b6e20
             grind)
          | exact resolve b6e1768 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1768
        have b6e1841 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1167
             have i₂ := b6e1770
             grind)
          | exact superpose b6e1770 b6e1167
          | exact resolve b6e1167 b6e1770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1167 b6e1770
        have b6e1862 : x = y ∨ (σ x) = (σ y) := by grind
        clear b6e1841
        have b6e1864 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1862
             have r₂ := b6e21
             grind)
          | exact resolve b6e1862 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1862
        have b6e2082 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e1864
             grind)
          | exact superpose b6e1864 b6e13
          | exact resolve b6e13 b6e1864
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1864
        have b6e2112 : x = y := by
          first
          | (have i₁ := b6e2082
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2082
          | exact resolve b6e2082 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2082
        have b6e2114 : False := by grind
        exact b6e2114
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e13 X0 X2 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e789 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e79 x y
               grind)
            | exact superpose b8e79 b8e20
            | (have j1 := b8e79 x y
               grind)
            | exact resolve b8e20 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e818 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e79 y x
               grind)
            | exact superpose b8e79 b8e23
            | (have j1 := b8e79 y x
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e79 y x
               grind)
            | exact resolve b8e23 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e847 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b8e818
          have b8e852 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e847
               have r₂ := b8e24
               grind)
            | exact resolve b8e847 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e847
          have b8e857 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e789
               have r₂ := b8e24
               grind)
            | exact resolve b8e789 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e789
          have b8e863 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b8e857
               have i₂ := b8e852
               grind)
            | exact superpose b8e852 b8e857
            | exact resolve b8e857 b8e852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e857
          have b8e865 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ (k x y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e13 (σ y) X0 (σ x)
               have i₂ := b8e852
               grind)
            | exact superpose b8e852 b8e13
            | exact resolve b8e13 b8e852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = y ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e863
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e863
            | (have j1 := b8e18 (σ x) (σ (k x y))
               grind)
            | (have r₁ := b8e863
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e863
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e863 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e863
          have b8e2025 : (σ x) = (σ (k x y)) ∨ x = y ∨ x = (M.op y x) := by grind
          clear b8e2024
          have b8e2026 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b8e2025
               have r₂ := b8e22
               grind)
            | exact resolve b8e2025 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2025
          have b8e2210 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e14 (k x y)
               have i₂ := b8e2026
               grind)
            | exact superpose b8e2026 b8e14
            | exact resolve b8e14 b8e2026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2026
          have b8e2240 : x = (k x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e2210
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e2210
            | exact resolve b8e2210 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2210
          have b8e2420 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e18 x y
               have i₂ := b8e2240
               grind)
            | exact superpose b8e2240 b8e18
            | (have j0 := b8e18 x y
               grind)
            | exact resolve b8e18 b8e2240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2240
          have b8e2421 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by grind
          clear b8e2420
          have b8e2423 : x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e2421
               have r₂ := b8e22
               grind)
            | exact resolve b8e2421 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2421
          have b8e2425 : x = (M.op y x) := by
            first
            | (have r₁ := b8e2423
               have r₂ := b8e21
               grind)
            | exact resolve b8e2423 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2423
          have b8e2639 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e37 y X0 x
               have i₂ := b8e2425
               grind)
            | exact superpose b8e2425 b8e37
            | exact resolve b8e37 b8e2425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37
          have b8e2665 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e2639 X0
               have i₂ := b8e2425
               grind)
            | exact superpose b8e2425 b8e2639
            | exact resolve b8e2639 b8e2425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2639
          have b8e2919 : ∀ X1 : G, x = (M.op (M.op y X1) y) := by
            intro X1
            first
            | (have i₁ := b8e13 y x X1
               have i₂ := b8e2665 x
               grind)
            | exact superpose b8e2665 b8e13
            | exact resolve b8e13 b8e2665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3147 : x = (M.op x y) := by
            first
            | (have i₁ := b8e2919 (M.op y x)
               have i₂ := b8e2665 x
               grind)
            | exact superpose b8e2665 b8e2919
            | exact resolve b8e2919 b8e2665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2665 b8e2919
          have b8e33372 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ (M.op y x)) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e865 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e865
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e865 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e865
          have b8e33830 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ (M.op y x)) (σ y)) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e33372 X0
               grind)
            | (have r₁ := b8e33372 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e33372 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33372
          have b8e33878 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ (M.op y x)) (σ y)) := by
            intro X0
            first
            | (have j0 := b8e33830 X0
               grind)
            | (have r₁ := b8e33830 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e33830 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33830
          have b8e33903 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e33878 X0
               have i₂ := b8e2425
               grind)
            | exact superpose b8e2425 b8e33878
            | exact resolve b8e33878 b8e2425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33878
          have b8e34869 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have i₁ := b8e33903 (σ x)
               have i₂ := b8e852
               grind)
            | exact superpose b8e852 b8e33903
            | exact resolve b8e33903 b8e852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33903
          have b8e36348 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ x = y ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e34869
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e34869
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e34869 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34869
          have b8e36542 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e36348
               have r₂ := b8e22
               grind)
            | exact resolve b8e36348 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36348
          have b8e36576 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have r₁ := b8e36542
               have r₂ := b8e21
               grind)
            | exact resolve b8e36542 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36542
          have b8e36597 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e36576
               have i₂ := b8e2425
               grind)
            | exact superpose b8e2425 b8e36576
            | exact resolve b8e36576 b8e2425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36576
          have b8e36605 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e36597
               have i₂ := b8e852
               grind)
            | exact superpose b8e852 b8e36597
            | exact resolve b8e36597 b8e852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e852 b8e36597
          have b8e37650 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e36605
               grind)
            | exact superpose b8e36605 b8e20
            | exact resolve b8e20 b8e36605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36605
          have b8e37770 : (σ x) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e37650
               have i₂ := b8e3147
               grind)
            | exact superpose b8e3147 b8e37650
            | exact resolve b8e37650 b8e3147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3147 b8e37650
          have b8e39686 : (σ x) ≠ (σ (M.op y x)) ∨ x = y ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e37770
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e37770
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e37770
               have r₂ := b8e18 (σ x) (σ (k x y))
               grind)
            | (have r₁ := b8e37770
               have r₂ := b8e18 (σ (k x y)) (σ x)
               grind)
            | exact resolve b8e37770 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37770
          have b8e39690 : (σ x) ≠ (σ (M.op y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e39686
               have r₂ := b8e22
               grind)
            | exact resolve b8e39686 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39686
          have b8e39691 : (σ x) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b8e39690
               have r₂ := b8e21
               grind)
            | exact resolve b8e39690 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39690
          have b8e39692 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e39691
               have i₂ := b8e2425
               grind)
            | exact superpose b8e2425 b8e39691
            | exact resolve b8e39691 b8e2425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2425 b8e39691
          have b8e39693 : False := by grind
          exact b8e39693

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyy_x_pxy_Equation4404 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4404 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ x) ≠ (σ x) := by
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
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e39 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 y X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e39 x X2
             have i₂ := b1e39 x X0
             grind)
          | (have i₁ := b1e39 X0 x
             have i₂ := b1e39 X0 (M.op x X0)
             grind)
          | exact superpose b1e39 b1e39
          | exact resolve b1e39 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e127 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e46 y X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e46 X0 y
             grind)
          | exact superpose b1e46 b1e20
          | exact resolve b1e20 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e198 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e127 X0
             grind)
          | exact superpose b1e127 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x X0
             have r₂ := b1e127 X0
             grind)
          | exact resolve b1e15 b1e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e203 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e198 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198
        have b1e2798 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e84 x x
             grind)
          | exact superpose b1e84 b1e22
          | (have j1 := b1e84 x x
             grind)
          | exact resolve b1e22 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e2879 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e2798
        have b1e2933 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e2879
             have i₂ := b1e203 x
             grind)
          | exact superpose b1e203 b1e2879
          | exact resolve b1e2879 b1e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e203 b1e2879
        have b1e2983 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e2933
             have i₂ := b1e127 x
             grind)
          | exact superpose b1e127 b1e2933
          | exact resolve b1e2933 b1e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127 b1e2933
        have b1e3000 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e2983
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e2983
          | exact resolve b1e2983 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2983
        have b1e3001 : (σ x) = (σ y) := by grind
        clear b1e3000
        have b1e3019 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e3001
             grind)
          | exact superpose b1e3001 b1e21
          | exact resolve b1e21 b1e3001
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3037 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e3019
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e3019
          | exact resolve b1e3019 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3019
        have b1e3042 : False := by grind
        exact b1e3042
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e35 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 x X0 y X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b2e35 x X2
             have i₂ := b2e35 x X0
             grind)
          | (have i₁ := b2e35 X0 x
             have i₂ := b2e35 X0 (M.op x X0)
             grind)
          | exact superpose b2e35 b2e35
          | exact resolve b2e35 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e86 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e20
             have i₂ := b2e44 y X0
             grind)
          | (have i₁ := b2e20
             have i₂ := b2e44 X0 y
             grind)
          | exact superpose b2e44 b2e20
          | exact resolve b2e20 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e119 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e86 X0
             grind)
          | exact superpose b2e86 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x X0
             have r₂ := b2e86 X0
             grind)
          | exact resolve b2e15 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e124 : ∀ X0 : G, (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e119 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119
        have b2e140 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (k x X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 X0 X2
             have i₂ := b2e124 X0
             grind)
          | exact superpose b2e124 b2e12
          | exact resolve b2e12 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1380 : ∀ X0 X1 : G, (M.op X0 (k x X0)) = (M.op (k x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e140 X0 X0 X1
             have i₂ := b2e124 X0
             grind)
          | exact superpose b2e124 b2e140
          | exact resolve b2e140 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e140
        have b2e3308 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e99 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e3310 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e3308 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3308
        have b2e3325 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e3310 X0
             have i₂ := b2e124 (σ X0)
             grind)
          | exact superpose b2e124 b2e3310
          | (have j0 := b2e3310 X0
             grind)
          | exact resolve b2e3310 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3310
        have b2e6055 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k x (σ x)) := by
          first
          | (have i₁ := b2e3325 x
             have i₂ := b2e124 x
             grind)
          | exact superpose b2e124 b2e3325
          | (have j0 := b2e3325 x
             grind)
          | exact resolve b2e3325 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3325
        have b2e6064 : (σ x) ≠ (σ x) ∨ (σ x) = (k x (σ x)) := by
          first
          | (have i₁ := b2e6055
             have i₂ := b2e86 x
             grind)
          | exact superpose b2e86 b2e6055
          | exact resolve b2e6055 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86 b2e6055
        have b2e6065 : (σ x) = (k x (σ x)) := by grind
        clear b2e6064
        have b2e6093 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e1380 (σ x) x
             have i₂ := b2e6065
             grind)
          | exact superpose b2e6065 b2e1380
          | exact resolve b2e1380 b2e6065
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1380
        have b2e6100 : ∀ X0 : G, (M.op (σ x) X0) = (k x (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e6093 X0
             have i₂ := b2e124 (σ x)
             grind)
          | exact superpose b2e124 b2e6093
          | exact resolve b2e6093 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124 b2e6093
        have b2e6104 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e6100 X0
             have i₂ := b2e6065
             grind)
          | exact superpose b2e6065 b2e6100
          | exact resolve b2e6100 b2e6065
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6065 b2e6100
        have b2e6325 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e6104 (σ y)
             grind)
          | exact superpose b2e6104 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e6104 (σ y)
             grind)
          | exact resolve b2e21 b2e6104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6104
        have b2e6396 : False := by grind
        exact b2e6396
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e34 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ x) X0 (σ y) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e234 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e26 X1 X0
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e625 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (σ x) X2) := by
          intro X0 X2
          first
          | (have i₁ := b3e34 x X2
             have i₂ := b3e34 x X0
             grind)
          | (have i₁ := b3e34 X0 x
             have i₂ := b3e34 X0 (M.op (σ x) X0)
             grind)
          | exact superpose b3e34 b3e34
          | exact resolve b3e34 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e694 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e22
             have i₂ := b3e625 (σ y) X0
             grind)
          | (have i₁ := b3e22
             have i₂ := b3e625 X0 (σ y)
             grind)
          | exact superpose b3e625 b3e22
          | exact resolve b3e22 b3e625
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e625
        have b3e939 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e694 X0
             grind)
          | exact superpose b3e694 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) X0
             have r₂ := b3e694 X0
             grind)
          | exact resolve b3e15 b3e694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e952 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e939 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e939
        have b3e1817 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e234 x X0
             have i₂ := b3e952 X0
             grind)
          | exact superpose b3e952 b3e234
          | exact resolve b3e234 b3e952
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e234 b3e952
        have b3e1864 : (τ (σ x)) = (k x (τ (σ x))) := by
          first
          | (have i₁ := b3e1817 (σ x)
             have i₂ := b3e694 (σ x)
             grind)
          | exact superpose b3e694 b3e1817
          | exact resolve b3e1817 b3e694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e694 b3e1817
        have b3e1879 : x = (k x x) := by
          first
          | (have i₁ := b3e1864
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1864
          | exact resolve b3e1864 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1864
        have b3e2047 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e1879
             grind)
          | exact superpose b3e1879 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e1879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1879
        have b3e2048 : x = (M.op x x) := by grind
        clear b3e2047
        have b3e2152 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e2048
             grind)
          | exact superpose b3e2048 b3e21
          | exact resolve b3e21 b3e2048
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2195 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e2152
             grind)
          | exact superpose b3e2152 b3e20
          | exact resolve b3e20 b3e2152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2152
        have b3e2214 : False := by grind
        exact b3e2214
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e34 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ x) (σ x) X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e40 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e40
            | exact resolve b4e40 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op x X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 x x X2 X3
               have i₂ := b4e40 x X0
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e57 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (k (M.op X0 X2) X3) = (M.op X3 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16 (M.op X0 X2) X3
               have i₂ := b4e13 X0 X1 X2 X3
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X0 X2) X3
               grind)
            | (have r₁ := b4e16 (M.op X0 (M.op X0 X1)) X3
               have r₂ := b4e13 X0 X1 (M.op X0 X1) X3
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X1 X2 : G, (M.op x y) = (M.op (M.op y X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b4e13 y x X1 X2
               have i₂ := b4e43 (M.op y x)
               grind)
            | exact superpose b4e43 b4e13
            | exact resolve b4e13 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) X2) := by
            intro X2
            first
            | (have i₁ := b4e70 x X2
               have i₂ := b4e43 x
               grind)
            | exact superpose b4e43 b4e70
            | exact resolve b4e70 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e200 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 x
               have i₂ := b4e50 x X0 X1
               grind)
            | exact superpose b4e50 b4e43
            | exact resolve b4e43 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e477 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b4e16 (M.op x y) X0
               have i₂ := b4e71 X0
               grind)
            | exact superpose b4e71 b4e16
            | (have j0 := b4e16 (M.op x y) X0
               grind)
            | (have r₁ := b4e16 (M.op x y) x
               have r₂ := b4e71 x
               grind)
            | exact resolve b4e16 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e487 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) X0) := by
            intro X0
            first
            | (have j0 := b4e477 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e477
          have b4e490 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e679 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e200 X0 (M.op x X0)
               have i₂ := b4e487 (M.op x X0)
               grind)
            | exact superpose b4e487 b4e200
            | exact resolve b4e200 b4e487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e200
          have b4e683 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e27 X0 (M.op x y)
               have i₂ := b4e487 (τ X0)
               grind)
            | exact superpose b4e487 b4e27
            | exact resolve b4e27 b4e487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e1437 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e490 X0
               grind)
            | exact superpose b4e490 b4e20
            | exact resolve b4e20 b4e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e490
          have b4e1894 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e57 X0 X1 (M.op X0 X1) X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e4393 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e90 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e4395 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e4393 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4393
          have b4e5054 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 (k (M.op x y) X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e1894 X0 X0 X1
               have i₂ := b4e487 X0
               grind)
            | exact superpose b4e487 b4e1894
            | exact resolve b4e1894 b4e487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1894
          have b4e18069 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e4395 (M.op x y)
               have i₂ := b4e679 y
               grind)
            | exact superpose b4e679 b4e4395
            | (have j0 := b4e4395 (M.op x y)
               grind)
            | exact resolve b4e4395 b4e679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e679 b4e4395
          have b4e18089 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
          clear b4e18069
          have b4e18112 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e18089
               have i₂ := b4e487 (σ (M.op x y))
               grind)
            | exact superpose b4e487 b4e18089
            | exact resolve b4e18089 b4e487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18089
          have b4e33381 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
            intro X0
            first
            | (have i₁ := b4e5054 (σ (M.op x y)) X0
               have i₂ := b4e18112
               grind)
            | exact superpose b4e18112 b4e5054
            | exact resolve b4e5054 b4e18112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5054
          have b4e33395 : ∀ X0 : G, (M.op X0 X0) = (k (k (M.op x y) (σ (M.op x y))) X0) := by
            intro X0
            first
            | (have i₁ := b4e33381 X0
               have i₂ := b4e487 (σ (M.op x y))
               grind)
            | exact superpose b4e487 b4e33381
            | exact resolve b4e33381 b4e487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e487 b4e33381
          have b4e33398 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e33395 X0
               have i₂ := b4e18112
               grind)
            | exact superpose b4e18112 b4e33395
            | exact resolve b4e33395 b4e18112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18112 b4e33395
          have b4e34272 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e683 X0
               have i₂ := b4e33398 X0
               grind)
            | exact superpose b4e33398 b4e683
            | exact resolve b4e683 b4e33398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e683 b4e33398
          have b4e34663 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e34272 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e34272
            | exact resolve b4e34272 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34272
          have b4e35600 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1437 (σ y)
               have i₂ := b4e34663 y
               grind)
            | exact superpose b4e34663 b4e1437
            | exact resolve b4e1437 b4e34663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1437 b4e34663
          have b4e35755 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e35600
               have i₂ := b4e43 y
               grind)
            | exact superpose b4e43 b4e35600
            | exact resolve b4e35600 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e35600
          have b4e35756 : False := by grind
          exact b4e35756
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e72 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b5e77 : x = (k x y) := by
            first
            | (have r₁ := b5e72
               have r₂ := b5e21
               grind)
            | exact resolve b5e72 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e90 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2138 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e90 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e2139 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2138
               have r₂ := b5e23
               grind)
            | exact resolve b5e2138 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2138
          have b5e2140 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2139
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2139
            | exact resolve b5e2139 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2139
          have b5e2141 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2140
               have i₂ := b5e77
               grind)
            | exact superpose b5e77 b5e2140
            | exact resolve b5e2140 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e2140
          have b5e2142 : False := by grind
          exact b5e2142
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (σ x) (σ y) X0 X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 X1 x x
             have i₂ := b6e12 X0 X2 x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e199 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e27 (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e27
          | exact resolve b6e27 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e235 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e199 (σ y)
             grind)
          | exact superpose b6e199 b6e22
          | exact resolve b6e22 b6e199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199
        have b6e314 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e235
             grind)
          | exact superpose b6e235 b6e15
          | (have r₁ := b6e15 (σ x) (σ x)
             have r₂ := b6e235
             grind)
          | exact resolve b6e15 b6e235
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e235
        have b6e321 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b6e314
        have b6e322 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e321
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e321
          | exact resolve b6e321 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e321
        have b6e595 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e322
             grind)
          | exact superpose b6e322 b6e13
          | exact resolve b6e13 b6e322
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e322
        have b6e597 : x = (k x x) := by
          first
          | (have i₁ := b6e595
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e595
          | exact resolve b6e595 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e595
        have b6e747 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e597
             grind)
          | exact superpose b6e597 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e597
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e597
        have b6e748 : x = (M.op x x) := by grind
        clear b6e747
        have b6e932 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e35 x X0 x
             have i₂ := b6e748
             grind)
          | exact superpose b6e748 b6e35
          | exact resolve b6e35 b6e748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e936 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e932 X0
             have i₂ := b6e748
             grind)
          | exact superpose b6e748 b6e932
          | exact resolve b6e932 b6e748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e748 b6e932
        have b6e1032 : ∀ X1 X2 : G, x = (M.op (M.op x X1) X2) := by
          intro X1 X2
          first
          | (have i₁ := b6e12 x x X1 X2
             have i₂ := b6e936 x
             grind)
          | exact superpose b6e936 b6e12
          | exact resolve b6e12 b6e936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1121 : ∀ X1 : G, x = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b6e1032 (M.op x x) X1
             have i₂ := b6e936 x
             grind)
          | exact superpose b6e936 b6e1032
          | exact resolve b6e1032 b6e936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e936 b6e1032
        have b6e1203 : x ≠ x := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e1121 y
             grind)
          | exact superpose b6e1121 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e1121 y
             grind)
          | exact resolve b6e20 b6e1121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1121
        have b6e1232 : False := by grind
        exact b6e1232
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e62 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e23
               grind)
            | exact resolve b7e62 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
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
          clear b7e67
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
          have b7e95 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
          have b7e96 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e95
          have b7e98 : y = (M.op x x) := by
            first
            | (have r₁ := b7e96
               have r₂ := b7e21
               grind)
            | exact resolve b7e96 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e100 : False := by grind
          exact b7e100
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e88 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1347 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e88 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e1348 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1347
               have r₂ := b8e23
               grind)
            | exact resolve b8e1347 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1347
          have b8e1349 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1348
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1348
            | exact resolve b8e1348 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1348
          have b8e1350 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1349
               grind)
            | exact superpose b8e1349 b8e20
            | exact resolve b8e20 b8e1349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1349
          have b8e1920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1350
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1350
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1350 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1350
          have b8e1921 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e1920
          have b8e1923 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1921
               have r₂ := b8e22
               grind)
            | exact resolve b8e1921 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1921
          have b8e1925 : False := by grind
          exact b8e1925

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4407 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
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
      have b0e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X1 X0) X1 X3
           have i₂ := b0e11 X1 X0 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
      have b0e45 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e39 X0 X1 X2 X3
           have i₂ := b0e11 X0 X1 (M.op (M.op X1 X0) X1)
           grind)
        | exact superpose b0e11 b0e39
        | exact resolve b0e39 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e48 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e11
        | exact resolve b0e11 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e48 X0 x
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e48
        | exact resolve b0e48 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e50 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e42 (M.op y x)
           grind)
        | exact superpose b0e42 b0e49
        | exact resolve b0e49 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e67 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X2
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X0 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op X2 X1)
           have i₂ := b0e16 (M.op X2 X1) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op (M.op X1 X0) X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e74 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X0 (M.op X0 X1)
           have i₂ := b0e16 X2 (M.op X0 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 (M.op X0 X1)
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e20
           have i₂ := b0e16 X0 (σ x)
           grind)
        | exact superpose b0e16 b0e20
        | (have j1 := b0e16 X0 (σ x)
           grind)
        | exact resolve b0e20 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e86 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X0) X1) = (M.op X0 (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (M.op X0 y) X1
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e11
        | exact resolve b0e11 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e87 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op (M.op X1 X0) y)
           have i₂ := b0e50 (M.op X1 X0)
           grind)
        | exact superpose b0e50 b0e11
        | exact resolve b0e11 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e88 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e86 X0 x
           have i₂ := b0e45 X0 y X0 x
           grind)
        | exact superpose b0e45 b0e86
        | exact resolve b0e86 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86
      have b0e93 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e88 X0
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e88
        | exact resolve b0e88 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e104 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      clear b0e26
      have b0e113 : (M.op x y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e87 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e87
        | exact resolve b0e87 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op x y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e87 X0 X1
           grind)
        | exact superpose b0e87 b0e11
        | exact resolve b0e11 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e127 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e41
        | exact resolve b0e41 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e133 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e18
        | exact resolve b0e18 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e138 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e16 (σ y) X0
           have i₂ := b0e41 (σ y)
           grind)
        | exact superpose b0e41 b0e16
        | (have j0 := b0e16 X0 X0
           grind)
        | exact resolve b0e16 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e153 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e138 X0
           have i₂ := b0e113
           grind)
        | exact superpose b0e113 b0e138
        | (have j0 := b0e138 X0
           grind)
        | exact resolve b0e138 b0e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e138
      have b0e199 : ∀ X0 : G, (M.op x y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e50 (σ y)
           have i₂ := b0e127 (M.op (σ y) y) X0
           grind)
        | (have i₁ := b0e50 (σ y)
           have i₂ := b0e127 X0 (M.op (σ y) y)
           grind)
        | exact superpose b0e127 b0e50
        | exact resolve b0e50 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127
      have b0e493 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e133 (M.op (σ y) y)
           have i₂ := b0e50 (σ y)
           grind)
        | exact superpose b0e50 b0e133
        | exact resolve b0e133 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e133
      have b0e679 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (M.op X3 X3) ∨ (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e15 X3 (M.op (M.op X0 X1) X2)
           have i₂ := b0e45 X0 X1 X2 (M.op (M.op X0 X1) X2)
           grind)
        | exact superpose b0e45 b0e15
        | (have j0 := b0e15 X3 (M.op (M.op X0 X1) X2)
           grind)
        | exact resolve b0e15 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e707 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op x y) ∨ (M.op (M.op X0 X1) X2) = (M.op X3 X3) ∨ (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e679 X0 X1 X2 X3
           have i₂ := b0e117 X1 X0 X2
           grind)
        | exact superpose b0e117 b0e679
        | (have j0 := b0e679 X0 X1 X2 X3
           grind)
        | exact resolve b0e679 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e679
      have b0e765 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 X3) ∨ (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e707 X0 X1 X2 X3
           grind)
        | (have r₁ := b0e707 X0 X1 X2 X3
           have r₂ := b0e87 X0 X1
           grind)
        | exact resolve b0e707 b0e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87 b0e707
      have b0e778 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op X3 X3) ∨ (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e765 X0 X1 X2 X3
           have i₂ := b0e117 X1 X0 X2
           grind)
        | exact superpose b0e117 b0e765
        | (have j0 := b0e765 X0 X1 X2 X3
           grind)
        | exact resolve b0e765 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e765
      have b0e781 : ∀ X3 : G, (k X3 (M.op x y)) = X3 ∨ (M.op x y) = (M.op X3 X3) := by
        intro X3
        first
        | (have i₁ := b0e778 x x x X3
           have i₂ := b0e117 x x x
           grind)
        | exact superpose b0e117 b0e778
        | (have j0 := b0e778 x x x X3
           grind)
        | exact resolve b0e778 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117 b0e778
      have b0e1714 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      clear b0e65
      have b0e1967 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e104
      have b0e1979 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1967 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1967
        | exact resolve b0e1967 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1967
      have b0e2298 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e67 X0 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2299 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e67 X0 X1 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e3831 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e68 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e68
        | (have j0 := b0e68 X0 x x
           grind)
        | exact resolve b0e68 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3839 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op x y) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e68 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e68
        | (have j0 := b0e68 X0 x x
           grind)
        | exact resolve b0e68 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e4018 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e3839 X0
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e3839
        | (have j0 := b0e3839 X0
           grind)
        | exact resolve b0e3839 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3839
      have b0e4026 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e3831 X0
           have i₂ := b0e199 X0
           grind)
        | exact superpose b0e199 b0e3831
        | (have j0 := b0e3831 X0
           grind)
        | exact resolve b0e3831 b0e199
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3831
      have b0e4183 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e4026 X0
           have i₂ := b0e113
           grind)
        | exact superpose b0e113 b0e4026
        | (have j0 := b0e4026 X0
           grind)
        | exact resolve b0e4026 b0e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4026
      have b0e4519 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e76 x x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e76
        | exact resolve b0e76 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e4756 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
      clear b0e4519
      have b0e5687 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
        intro X0
        grind
      clear b0e781
      have b0e5741 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
        intro X0
        first
        | (have j0 := b0e5687 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5687
      have b0e5989 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e74 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e74
        | exact resolve b0e74 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e7900 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e1714 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1714
      have b0e7902 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e7900 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7900
      have b0e8102 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e2298 y x
           have i₂ := b0e42 x
           grind)
        | exact superpose b0e42 b0e2298
        | (have j0 := b0e2298 y x
           grind)
        | exact resolve b0e2298 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2298
      have b0e8104 : y = (M.op y y) ∨ (M.op y y) = (k y y) := by
        first
        | (have j1 := b0e5989 y
           grind)
        | (have r₁ := b0e8102
           have r₂ := b0e5989 x
           grind)
        | exact resolve b0e8102 b0e5989
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5989 b0e8102
      have b0e8124 : y = (M.op x y) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e8104
           have i₂ := b0e42 y
           grind)
        | exact superpose b0e42 b0e8104
        | exact resolve b0e8104 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8104
      have b0e8135 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e8124
           have i₂ := b0e42 y
           grind)
        | exact superpose b0e42 b0e8124
        | exact resolve b0e8124 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8124
      have b0e8204 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e2299 X0 (σ y)
           have i₂ := b0e199 X0
           grind)
        | exact superpose b0e199 b0e2299
        | (have j0 := b0e2299 X0 x
           grind)
        | (have r₁ := b0e2299 (M.op x y) (σ y)
           have r₂ := b0e199 (M.op x y)
           grind)
        | exact resolve b0e2299 b0e199
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e199
      have b0e8212 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e2299 X0 y
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e2299
        | (have j0 := b0e2299 X0 x
           grind)
        | (have r₁ := b0e2299 (M.op x y) y
           have r₂ := b0e42 (M.op x y)
           grind)
        | exact resolve b0e2299 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e2299
      have b0e8216 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e8212 X0
           have j1 := b0e4018 X0
           grind)
        | (have r₁ := b0e8212 (k y X0)
           have r₂ := b0e4018 X0
           grind)
        | (have r₁ := b0e8212 (M.op (M.op x y) (M.op x y))
           have r₂ := b0e4018 (M.op x y)
           grind)
        | (have r₁ := b0e8212 X0
           have r₂ := b0e4018 X0
           grind)
        | exact resolve b0e8212 b0e4018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4018 b0e8212
      have b0e8221 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x y) = (k (σ y) X0) := by
        intro X0
        first
        | (have j0 := b0e8204 X0
           have j1 := b0e4183 X0
           grind)
        | (have r₁ := b0e8204 (k (σ y) X0)
           have r₂ := b0e4183 X0
           grind)
        | (have r₁ := b0e8204 (M.op (M.op x y) (M.op x y))
           have r₂ := b0e4183 (M.op x y)
           grind)
        | (have r₁ := b0e8204 X0
           have r₂ := b0e4183 X0
           grind)
        | exact resolve b0e8204 b0e4183
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4183 b0e8204
      have b0e9308 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e7902 X0
           have i₂ := b0e8216 X0
           grind)
        | exact superpose b0e8216 b0e7902
        | (have j0 := b0e7902 X0
           have j1 := b0e8216 X0
           grind)
        | (have r₁ := b0e7902 X0
           have r₂ := b0e8216 X0
           grind)
        | exact resolve b0e7902 b0e8216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7902 b0e8216
      have b0e9381 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e9308 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9308
      have b0e16618 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op x y) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e1979 X0
           have i₂ := b0e8221 (σ X0)
           grind)
        | exact superpose b0e8221 b0e1979
        | (have j1 := b0e8221 (σ X0)
           grind)
        | exact resolve b0e1979 b0e8221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1979 b0e8221
      have b0e16700 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x y) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e16618 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e16618
        | (have j0 := b0e16618 X0
           grind)
        | exact resolve b0e16618 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16618
      have b0e16738 : ∀ X0 : G, (M.op x y) = (σ (k y X0)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16700 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e16700
        | (have j0 := b0e16700 X0
           grind)
        | exact resolve b0e16700 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16700
      have b0e21917 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16738 X0
           have i₂ := b0e9381 X0
           grind)
        | exact superpose b0e9381 b0e16738
        | (have j0 := b0e16738 X0
           have j1 := b0e9381 X0
           grind)
        | exact resolve b0e16738 b0e9381
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9381
      have b0e21921 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e16738 y
           have i₂ := b0e8135
           grind)
        | exact superpose b0e8135 b0e16738
        | exact resolve b0e16738 b0e8135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8135 b0e16738
      have b0e22105 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
      clear b0e21921
      have b0e22106 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e21917 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21917
      have b0e22189 : y = (M.op x y) := by
        first
        | (have r₁ := b0e22105
           have r₂ := b0e493
           grind)
        | exact resolve b0e22105 b0e493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22105
      have b0e22193 : ∀ X0 : G, (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e22106 X0
           grind)
        | (have r₁ := b0e22106 X0
           have r₂ := b0e493
           grind)
        | exact resolve b0e22106 b0e493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22106
      have b0e22808 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e93 X0
           have i₂ := b0e22189
           grind)
        | exact superpose b0e22189 b0e93
        | exact resolve b0e93 b0e22189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e22815 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e493
           have i₂ := b0e22189
           grind)
        | exact superpose b0e22189 b0e493
        | exact resolve b0e493 b0e22189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e493
      have b0e22820 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e5741 X0
           have i₂ := b0e22189
           grind)
        | exact superpose b0e22189 b0e5741
        | exact resolve b0e5741 b0e22189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5741
      have b0e23765 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16 X0 X0
           have i₂ := b0e22193 X0
           grind)
        | exact superpose b0e22193 b0e16
        | (have j0 := b0e16 X0 X0
           grind)
        | exact resolve b0e16 b0e22193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23792 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e153 (σ y)
           have i₂ := b0e22193 (σ y)
           grind)
        | exact superpose b0e22193 b0e153
        | (have j0 := b0e153 (σ y)
           grind)
        | exact resolve b0e153 b0e22193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e23801 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e4756
           have i₂ := b0e22193 x
           grind)
        | exact superpose b0e22193 b0e4756
        | exact resolve b0e4756 b0e22193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4756 b0e22193
      have b0e23810 : (σ x) = (σ y) := by grind
      clear b0e23801
      have b0e23813 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by grind
      clear b0e23792
      have b0e23831 : ∀ X0 : G, (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e23765 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23765
      have b0e23869 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e23813
           have i₂ := b0e41 (σ y)
           grind)
        | exact superpose b0e41 b0e23813
        | exact resolve b0e23813 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e23813
      have b0e23895 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e23869
           have i₂ := b0e113
           grind)
        | exact superpose b0e113 b0e23869
        | exact resolve b0e23869 b0e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113 b0e23869
      have b0e23896 : (M.op x y) = (σ y) := by grind
      clear b0e23895
      have b0e23905 : (M.op x y) = (σ x) := by
        first
        | (have i₁ := b0e23896
           have i₂ := b0e23810
           grind)
        | exact superpose b0e23810 b0e23896
        | exact resolve b0e23896 b0e23810
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23810 b0e23896
      have b0e23907 : y = (σ x) := by
        first
        | (have i₁ := b0e23905
           have i₂ := b0e22189
           grind)
        | exact superpose b0e22189 b0e23905
        | exact resolve b0e23905 b0e22189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22189 b0e23905
      have b0e23985 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y ∨ y = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e75 X0
           have i₂ := b0e23907
           grind)
        | exact superpose b0e23907 b0e75
        | exact resolve b0e75 b0e23907
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75 b0e23907
      have b0e24033 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have j0 := b0e23985 X0
           grind)
        | (have r₁ := b0e23985 X0
           have r₂ := b0e22815
           grind)
        | exact resolve b0e23985 b0e22815
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23985
      have b0e24046 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e24033 X0
           have i₂ := b0e22820 X0
           grind)
        | exact superpose b0e22820 b0e24033
        | (have j0 := b0e24033 X0
           grind)
        | exact resolve b0e24033 b0e22820
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22820 b0e24033
      have b0e24052 : ∀ X0 : G, y = X0 ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e24046 X0
           have i₂ := b0e22808 X0
           grind)
        | exact superpose b0e22808 b0e24046
        | (have j0 := b0e24046 X0
           grind)
        | exact resolve b0e24046 b0e22808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22808 b0e24046
      have b0e24056 : ∀ X0 : G, y = X0 ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e24052 X0
           have i₂ := b0e23831 X0
           grind)
        | exact superpose b0e23831 b0e24052
        | (have j0 := b0e24052 X0
           grind)
        | exact resolve b0e24052 b0e23831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23831 b0e24052
      have b0e24057 : ∀ X0 : G, y = X0 := by
        intro X0
        first
        | (have j0 := b0e24056 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24056
      have b0e26050 : y ≠ y := by
        first
        | (have i₁ := b0e22815
           have i₂ := b0e24057 (σ y)
           grind)
        | exact superpose b0e24057 b0e22815
        | (have r₁ := b0e22815
           have r₂ := b0e24057 (σ y)
           grind)
        | exact resolve b0e22815 b0e24057
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22815 b0e24057
      have b0e26210 : False := by grind
      exact b0e26210
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ y) = (k (σ y) (σ y)) := by grind
        have b1e26 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e25
          | exact resolve b1e25 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : y = (k y y) := by
          first
          | (have i₁ := b1e31
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e31
          | exact resolve b1e31 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X1) X3) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 (M.op X1 X0) X3
             have i₂ := b1e12 X1 X0 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X1 X0) X1 X3
             have i₂ := b1e12 X1 X0 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
        have b1e44 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
        have b1e45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 X1 (M.op (M.op X1 X2) X0)
             have i₂ := b1e12 (M.op X1 X2) X0 X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e43 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e43
          | exact resolve b1e43 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e48 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e41 X0 X1 X2 X3
             have i₂ := b1e12 X0 X1 (M.op (M.op X1 X0) X1)
             grind)
          | exact superpose b1e12 b1e41
          | exact resolve b1e41 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e51 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e44 X1
             have i₂ := b1e44 X0
             grind)
          | exact superpose b1e44 b1e44
          | exact resolve b1e44 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e97 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e32
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e32 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e100 : y = (M.op y y) := by grind
        clear b1e97
        have b1e133 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e100
             have i₂ := b1e51 y X0
             grind)
          | (have i₁ := b1e100
             have i₂ := b1e51 X0 y
             grind)
          | exact superpose b1e51 b1e100
          | exact resolve b1e100 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e100
        have b1e153 : y = (M.op x y) := by
          first
          | (have i₁ := b1e44 x
             have i₂ := b1e133 x
             grind)
          | exact superpose b1e133 b1e44
          | exact resolve b1e44 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e269 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ y) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e45 (σ y) X0 X1 X2
             have i₂ := b1e47 (M.op X0 X1)
             grind)
          | exact superpose b1e47 b1e45
          | exact resolve b1e45 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e270 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e45 y X0 X1 X2
             have i₂ := b1e133 (M.op X0 X1)
             grind)
          | exact superpose b1e133 b1e45
          | exact resolve b1e45 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e327 : ∀ X0 X1 : G, y = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e270 X0 X1 x
             have i₂ := b1e133 x
             grind)
          | exact superpose b1e133 b1e270
          | exact resolve b1e270 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e133 b1e270
        have b1e328 : ∀ X0 X1 : G, (σ y) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e269 X0 X1 x
             have i₂ := b1e47 x
             grind)
          | exact superpose b1e47 b1e269
          | exact resolve b1e269 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e269
        have b1e345 : y = (σ y) := by
          first
          | (have i₁ := b1e328 x x
             have i₂ := b1e327 x x
             grind)
          | exact superpose b1e327 b1e328
          | exact resolve b1e328 b1e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e328
        have b1e361 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e345
             grind)
          | exact superpose b1e345 b1e19
          | exact resolve b1e19 b1e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e367 : (σ y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e361
             have i₂ := b1e153
             grind)
          | exact superpose b1e153 b1e361
          | exact resolve b1e361 b1e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153 b1e361
        have b1e368 : y ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e367
             have i₂ := b1e345
             grind)
          | exact superpose b1e345 b1e367
          | exact resolve b1e367 b1e345
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e345 b1e367
        have b1e663 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X0 X1)) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e35 (M.op X0 X1) X2 x X3
             have i₂ := b1e48 X0 X1 X2 x
             grind)
          | exact superpose b1e48 b1e35
          | exact resolve b1e35 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e758 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e663 X0 X1 X2 x
             have i₂ := b1e48 X2 (M.op X0 X1) X2 x
             grind)
          | exact superpose b1e48 b1e663
          | exact resolve b1e663 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48 b1e663
        have b1e807 : ∀ X0 X1 X2 : G, y = (M.op X2 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e758 X0 X1 X2
             have i₂ := b1e327 (M.op X0 X1) X2
             grind)
          | exact superpose b1e327 b1e758
          | exact resolve b1e758 b1e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e758
        have b1e833 : ∀ X2 : G, y = (M.op X2 y) := by
          intro X2
          first
          | (have i₁ := b1e807 x x X2
             have i₂ := b1e327 x x
             grind)
          | exact superpose b1e327 b1e807
          | exact resolve b1e807 b1e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e327 b1e807
        have b1e886 : y ≠ y := by
          first
          | (have i₁ := b1e368
             have i₂ := b1e833 (σ x)
             grind)
          | exact superpose b1e833 b1e368
          | (have r₁ := b1e368
             have r₂ := b1e833 (σ x)
             grind)
          | exact resolve b1e368 b1e833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e368 b1e833
        have b1e891 : False := by grind
        exact b1e891
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X0 X3
             have i₂ := b2e12 X1 X0 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
        have b2e36 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1
          grind
        have b2e41 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X0 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y X1
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e41 X0 x
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e41
          | exact resolve b2e41 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e44 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b2e42 X0
             have i₂ := b2e32 (M.op y x)
             grind)
          | exact superpose b2e32 b2e42
          | exact resolve b2e42 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e192 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e30 X0 X1 (M.op (M.op X0 X1) y) X2
             have i₂ := b2e44 (M.op X0 X1)
             grind)
          | exact superpose b2e44 b2e30
          | exact resolve b2e30 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e193 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X1 X0) y)
             have i₂ := b2e44 (M.op X1 X0)
             grind)
          | exact superpose b2e44 b2e12
          | exact resolve b2e12 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e2427 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e75 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e2428 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2427
             have r₂ := b2e22
             grind)
          | exact resolve b2e2427 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2427
        have b2e2429 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2428
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2428
          | exact resolve b2e2428 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2428
        have b2e2430 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e2429
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e2429
          | exact resolve b2e2429 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e2429
        have b2e2443 : ∀ X0 : G, (M.op x y) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e192 (σ x) (σ y) X0
             have i₂ := b2e2430
             grind)
          | exact superpose b2e2430 b2e192
          | exact resolve b2e192 b2e2430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e192
        have b2e3308 : (M.op x y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e2443 (σ x)
             grind)
          | exact superpose b2e2443 b2e21
          | exact resolve b2e21 b2e2443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3309 : (M.op x y) = (σ x) := by
          first
          | (have i₁ := b2e2430
             have i₂ := b2e2443 (σ y)
             grind)
          | exact superpose b2e2443 b2e2430
          | exact resolve b2e2430 b2e2443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2430 b2e2443
        have b2e3364 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e3308
             have i₂ := b2e3309
             grind)
          | exact superpose b2e3309 b2e3308
          | exact resolve b2e3308 b2e3309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3308
        have b2e3752 : ∀ X0 : G, (σ x) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e32 X0
             have i₂ := b2e3309
             grind)
          | exact superpose b2e3309 b2e32
          | exact resolve b2e32 b2e3309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e3761 : (M.op y x) = (k (M.op y x) (M.op x (σ x))) := by
          first
          | (have i₁ := b2e36 x y
             have i₂ := b2e3309
             grind)
          | exact superpose b2e3309 b2e36
          | exact resolve b2e36 b2e3309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e3766 : (σ x) = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e193 x y
             have i₂ := b2e3309
             grind)
          | exact superpose b2e3309 b2e193
          | exact resolve b2e193 b2e3309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193 b2e3309
        have b2e3772 : (M.op y x) = (k (M.op y x) (σ x)) := by
          first
          | (have i₁ := b2e3761
             have i₂ := b2e3766
             grind)
          | exact superpose b2e3766 b2e3761
          | exact resolve b2e3761 b2e3766
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3761 b2e3766
        have b2e3778 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3772
             have i₂ := b2e3752 x
             grind)
          | exact superpose b2e3752 b2e3772
          | exact resolve b2e3772 b2e3752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3752 b2e3772
        have b2e3780 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e3778
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e3778
          | exact resolve b2e3778 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3778
        have b2e7671 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e3780
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e3780
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e3780 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3780
        have b2e7687 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b2e7671
        have b2e7701 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e7687
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7687
          | exact resolve b2e7687 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7687
        have b2e7710 : x = (M.op x x) := by
          first
          | (have r₁ := b2e7701
             have r₂ := b2e3364
             grind)
          | exact resolve b2e7701 b2e3364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7701
        have b2e7719 : x = y := by
          first
          | (have i₁ := b2e7710
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e7710
          | exact resolve b2e7710 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7710
        have b2e7776 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e3364
             have i₂ := b2e7719
             grind)
          | exact superpose b2e7719 b2e3364
          | exact resolve b2e3364 b2e7719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3364 b2e7719
        have b2e7783 : False := by grind
        exact b2e7783
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X1 X0) X1 X3
             have i₂ := b3e12 X1 X0 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
        have b3e47 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e44 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e44
          | exact resolve b3e44 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e48 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e41 X0 X1 X2 X3
             have i₂ := b3e12 X0 X1 (M.op (M.op X1 X0) X1)
             grind)
          | exact superpose b3e12 b3e41
          | exact resolve b3e41 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e52 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 y X1
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e12
          | exact resolve b3e12 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e52 X0 x
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e52
          | exact resolve b3e52 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e57 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e47 y
             grind)
          | exact superpose b3e47 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e47 y
             grind)
          | exact resolve b3e16 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e58 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e67 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op X0 y) X1
             have i₂ := b3e53 X0
             grind)
          | exact superpose b3e53 b3e12
          | exact resolve b3e12 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (M.op (M.op X1 X0) y)
             have i₂ := b3e53 (M.op X1 X0)
             grind)
          | exact superpose b3e53 b3e12
          | exact resolve b3e12 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e69 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e67 X0 x
             have i₂ := b3e48 X0 y X0 x
             grind)
          | exact superpose b3e48 b3e67
          | exact resolve b3e67 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e67
        have b3e74 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e69 X0
             have i₂ := b3e53 X0
             grind)
          | exact superpose b3e53 b3e69
          | exact resolve b3e69 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e69
        have b3e90 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op X2 X1)
             have i₂ := b3e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X1 X0) X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e106 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X0 X0) = X0 ∨ y = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e90 X0 X1 X2
             have i₂ := b3e68 X1 X2
             grind)
          | exact superpose b3e68 b3e90
          | (have j0 := b3e90 X0 X1 X2
             grind)
          | exact resolve b3e90 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e134 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e68 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e68
          | exact resolve b3e68 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e139 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = y := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e68 X0 X1
             grind)
          | exact superpose b3e68 b3e12
          | exact resolve b3e12 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e156 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e134
             grind)
          | exact superpose b3e134 b3e19
          | exact resolve b3e19 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e162 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e156
             have i₂ := b3e74 x
             grind)
          | exact superpose b3e74 b3e156
          | exact resolve b3e156 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74 b3e156
        have b3e169 : ∀ X0 : G, y = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e134
             have i₂ := b3e43 X0
             grind)
          | exact superpose b3e43 b3e134
          | exact resolve b3e134 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e134
        have b3e1599 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          grind
        clear b3e58
        have b3e1630 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e1599 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1599
        have b3e1647 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0 y
             have i₂ := b3e1630 (τ X0)
             grind)
          | exact superpose b3e1630 b3e27
          | exact resolve b3e27 b3e1630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e1630
        have b3e1648 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e1647 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e1647
          | exact resolve b3e1647 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1647
        have b3e2850 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b3e1648 (M.op X0 X1)
             have i₂ := b3e106 (σ y) X1 X0
             grind)
          | exact superpose b3e106 b3e1648
          | (have j1 := b3e106 (σ y) X1 x
             grind)
          | exact resolve b3e1648 b3e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106 b3e1648
        have b3e2932 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have j0 := b3e2850 X0 X1
             grind)
          | (have r₁ := b3e2850 X0 X1
             have r₂ := b3e162
             grind)
          | exact resolve b3e2850 b3e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2850
        have b3e2970 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e2932 X0 X1
             have i₂ := b3e139 X1 X0 (σ y)
             grind)
          | exact superpose b3e139 b3e2932
          | exact resolve b3e2932 b3e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e139 b3e2932
        have b3e2976 : ∀ X0 X1 : G, y = (σ y) ∨ (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e2970 X0 X1
             have i₂ := b3e169 (σ y)
             grind)
          | exact superpose b3e169 b3e2970
          | (have j0 := b3e2970 X0 X1
             grind)
          | exact resolve b3e2970 b3e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e169 b3e2970
        have b3e2978 : ∀ X0 X1 : G, (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have j0 := b3e2976 X0 X1
             grind)
          | (have r₁ := b3e2976 X0 X1
             have r₂ := b3e162
             grind)
          | exact resolve b3e2976 b3e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e162 b3e2976
        have b3e3062 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e2978 x x
             grind)
          | exact superpose b3e2978 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e2978 x x
             grind)
          | exact resolve b3e20 b3e2978
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2978
        have b3e3063 : False := by grind
        exact b3e3063
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X1 X0) X1 X3
               have i₂ := b4e13 X1 X0 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
          have b4e46 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b4e49 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e46 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e46
            | exact resolve b4e46 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e50 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e45 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e45
            | exact resolve b4e45 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e51 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e43 X0 X1 X2 X3
               have i₂ := b4e13 X0 X1 (M.op (M.op X1 X0) X1)
               grind)
            | exact superpose b4e13 b4e43
            | exact resolve b4e43 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y X1
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e13
            | exact resolve b4e13 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e56 X0 x
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e56
            | exact resolve b4e56 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e56
          have b4e117 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X0 y) X1
               have i₂ := b4e57 X0
               grind)
            | exact superpose b4e57 b4e13
            | exact resolve b4e13 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e119 : y = (σ y) := by
            first
            | (have i₁ := b4e50 (M.op (σ y) y)
               have i₂ := b4e57 (σ y)
               grind)
            | exact superpose b4e57 b4e50
            | exact resolve b4e50 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e120 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e117 X0 x
               have i₂ := b4e51 X0 y X0 x
               grind)
            | exact superpose b4e51 b4e117
            | exact resolve b4e117 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e117
          have b4e126 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e120 X0
               have i₂ := b4e57 X0
               grind)
            | exact superpose b4e57 b4e120
            | exact resolve b4e120 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57 b4e120
          have b4e138 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e119
               grind)
            | exact superpose b4e119 b4e20
            | exact resolve b4e20 b4e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e143 : y ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e138
               have i₂ := b4e126 (σ x)
               grind)
            | exact superpose b4e126 b4e138
            | exact resolve b4e138 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e144 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e143
               have i₂ := b4e126 x
               grind)
            | exact superpose b4e126 b4e143
            | exact resolve b4e143 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126 b4e143
          have b4e145 : False := by grind
          exact b4e145
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e40 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b5e46 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e40 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40
            | exact resolve b5e40 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e50 : ∀ X0 X1 : G, (M.op X0 (M.op X0 y)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e46 X0
               grind)
            | exact superpose b5e46 b5e13
            | exact resolve b5e13 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e50 X0 x
               have i₂ := b5e46 x
               grind)
            | exact superpose b5e46 b5e50
            | exact resolve b5e50 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e53 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e46 y
               grind)
            | exact superpose b5e46 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e46 y
               grind)
            | exact resolve b5e17 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e55 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e53 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e65 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X1 X0) y)
               have i₂ := b5e51 (M.op X1 X0)
               grind)
            | exact superpose b5e51 b5e13
            | exact resolve b5e13 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e84 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X2 X1)
               have i₂ := b5e18 (M.op X2 X1) X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op (M.op X1 X0) X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e102 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X0 X0) = X0 ∨ y = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e84 X0 X1 X2
               have i₂ := b5e65 X1 X2
               grind)
            | exact superpose b5e65 b5e84
            | (have j0 := b5e84 X0 X1 X2
               grind)
            | exact resolve b5e84 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e136 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = y := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e65 X0 X1
               grind)
            | exact superpose b5e65 b5e13
            | exact resolve b5e13 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e1029 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e55
          have b5e1057 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e1029 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1029
          have b5e1412 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e1057 (τ X0)
               grind)
            | exact superpose b5e1057 b5e27
            | exact resolve b5e27 b5e1057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e1413 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1412 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1412
            | exact resolve b5e1412 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1412
          have b5e1812 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e85 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e1813 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1812
               have r₂ := b5e24
               grind)
            | exact resolve b5e1812 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1812
          have b5e1814 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1813
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1813
            | exact resolve b5e1813 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1813
          have b5e1815 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1814
               have i₂ := b5e1057 x
               grind)
            | exact superpose b5e1057 b5e1814
            | exact resolve b5e1814 b5e1057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1057 b5e1814
          have b5e1829 : ∀ X0 : G, y = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e136 (σ y) (σ x) X0
               have i₂ := b5e1815
               grind)
            | exact superpose b5e1815 b5e136
            | exact resolve b5e136 b5e1815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1815
          have b5e2262 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1829 (σ x)
               grind)
            | exact superpose b5e1829 b5e23
            | exact resolve b5e23 b5e1829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1829
          have b5e2707 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b5e1413 (M.op X0 X1)
               have i₂ := b5e102 (σ y) X1 X0
               grind)
            | exact superpose b5e102 b5e1413
            | (have j1 := b5e102 (σ y) X1 x
               grind)
            | exact resolve b5e1413 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102 b5e1413
          have b5e2785 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ y = (σ y) := by
            intro X0 X1
            first
            | (have j0 := b5e2707 X0 X1
               grind)
            | (have r₁ := b5e2707 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e2707 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2707
          have b5e2827 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e2785 X0 X1
               grind)
            | (have r₁ := b5e2785 X0 X1
               have r₂ := b5e2262
               grind)
            | exact resolve b5e2785 b5e2262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2262 b5e2785
          have b5e2835 : ∀ X0 X1 : G, (M.op X0 X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e2827 X0 X1
               have i₂ := b5e136 X1 X0 (σ y)
               grind)
            | exact superpose b5e136 b5e2827
            | exact resolve b5e2827 b5e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e136 b5e2827
          have b5e3593 : y ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e2835 x x
               grind)
            | exact superpose b5e2835 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e2835 x x
               grind)
            | exact resolve b5e21 b5e2835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2835
          have b5e3594 : False := by grind
          exact b5e3594
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
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
        have b6e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X0 X3
             have i₂ := b6e12 X1 X0 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b6e97 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e101 : x = (M.op x y) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e97
             have r₂ := b6e20
             grind)
          | exact resolve b6e97 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e104 : x = (M.op x y) := by
          first
          | (have r₁ := b6e101
             have r₂ := b6e21
             grind)
          | exact resolve b6e101 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e122 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 x y x x
             have i₂ := b6e104
             grind)
          | exact superpose b6e104 b6e43
          | exact resolve b6e43 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e236 : ∀ X0 : G, y ≠ (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e122 x X0
             grind)
          | (have i₁ := b6e20
             have i₂ := b6e122 X0 x
             grind)
          | exact superpose b6e122 b6e20
          | exact resolve b6e20 b6e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e238 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e104
             have i₂ := b6e122 y X0
             grind)
          | (have i₁ := b6e104
             have i₂ := b6e122 X0 y
             grind)
          | exact superpose b6e122 b6e104
          | exact resolve b6e104 b6e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104 b6e122
        have b6e245 : x ≠ y := by
          first
          | (have i₁ := b6e236 x
             have i₂ := b6e238 x
             grind)
          | exact superpose b6e238 b6e236
          | exact resolve b6e236 b6e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e236
        have b6e398 : x = (k x x) := by grind
        clear b6e238
        have b6e3897 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e95 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e95
          | exact resolve b6e95 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e4118 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3897
        have b6e4195 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4118
             have i₂ := b6e398
             grind)
          | exact superpose b6e398 b6e4118
          | exact resolve b6e4118 b6e398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e398 b6e4118
        have b6e4196 : (σ x) = (σ y) := by grind
        clear b6e4195
        have b6e4255 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e4196
             grind)
          | exact superpose b6e4196 b6e13
          | exact resolve b6e13 b6e4196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4196
        have b6e4269 : x = y := by
          first
          | (have i₁ := b6e4255
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e4255
          | exact resolve b6e4255 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4255
        have b6e4276 : False := by grind
        exact b6e4276
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ y) = (k (σ y) (σ y)) := by grind
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
          have b7e109 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e112 : y = (M.op y y) := by grind
          clear b7e109
          have b7e116 : False := by grind
          exact b7e116
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1541 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e1542 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1541
               have r₂ := b8e24
               grind)
            | exact resolve b8e1541 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1541
          have b8e1543 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1542
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1542
            | exact resolve b8e1542 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1542
          have b8e1544 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1543
               grind)
            | exact superpose b8e1543 b8e20
            | exact resolve b8e20 b8e1543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1543
          have b8e1569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1544
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1544
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1544 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1544
          have b8e1570 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1569
          have b8e1573 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1570
               have r₂ := b8e21
               grind)
            | exact resolve b8e1570 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1570
          have b8e1576 : False := by grind
          exact b8e1576

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation4407 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
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
      have b0e66 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e69 : False := by grind
      exact b0e69
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X0 X3
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op x X0) := by
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
          have b5e50 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e44 X1
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e44
            | exact resolve b5e44 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e84 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e50 y X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e50 X0 y
               grind)
            | exact superpose b5e50 b5e22
            | exact resolve b5e22 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e109 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 x X1
               have i₂ := b5e84 X0
               grind)
            | exact superpose b5e84 b5e13
            | exact resolve b5e13 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e111 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e109 X0 x
               have i₂ := b5e84 x
               grind)
            | exact superpose b5e84 b5e109
            | exact resolve b5e109 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e109
          have b5e132 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = x := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X1 X0) x)
               have i₂ := b5e111 (M.op X1 X0)
               grind)
            | exact superpose b5e111 b5e13
            | exact resolve b5e13 b5e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e176 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e111 (M.op X0 X1)
               have i₂ := b5e42 X0 X1 (M.op (M.op X0 X1) x) X2
               grind)
            | (have i₁ := b5e111 (M.op X0 X1)
               have i₂ := b5e42 X0 X1 X2 (M.op (M.op X0 X1) x)
               grind)
            | exact superpose b5e42 b5e111
            | exact resolve b5e111 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e111
          have b5e549 : ∀ X0 X1 : G, x = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e176 (σ X0) (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e176
            | exact resolve b5e176 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e176
          have b5e1238 : ∀ X0 : G, x = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e31 (M.op X0 X0)
               have i₂ := b5e549 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e549 b5e31
            | exact resolve b5e31 b5e549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e549
          have b5e1273 : ∀ X0 : G, x = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e1238 X0
               have i₂ := b5e13 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e13 b5e1238
            | exact resolve b5e1238 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1238
          have b5e1286 : x = (σ x) := by
            first
            | (have i₁ := b5e1273 x
               have i₂ := b5e132 x x
               grind)
            | exact superpose b5e132 b5e1273
            | exact resolve b5e1273 b5e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132 b5e1273
          have b5e1365 : x ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1286
               grind)
            | exact superpose b5e1286 b5e24
            | exact resolve b5e24 b5e1286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1286
          have b5e1371 : False := by grind
          exact b5e1371
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
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b7e52 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e55 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e52
          have b7e56 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e23
               grind)
            | exact resolve b7e55 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e57 : (σ x) = (σ (k x y)) := by
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
          have b7e67 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e57
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e57 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e68 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e26
               grind)
            | exact resolve b7e67 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e67
          have b7e69 : x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e70 : False := by grind
          exact b7e70
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e884 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e906 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e884
               have r₂ := b8e24
               grind)
            | exact resolve b8e884 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e884
          have b8e911 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e906
               have r₂ := b8e23
               grind)
            | exact resolve b8e906 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e906
          have b8e914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e911
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e911
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e911
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e911
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e911 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e911
          have b8e915 : x = (M.op x y) ∨ x = y := by grind
          clear b8e914
          have b8e916 : x = y := by
            first
            | (have r₁ := b8e915
               have r₂ := b8e22
               grind)
            | exact resolve b8e915 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e915
          have b8e917 : False := by grind
          exact b8e917
