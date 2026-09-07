import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4392`: `x ◇ (x ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pyx_Equation4392 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4392 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4392.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e67 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e72 : False := by grind
      exact b0e72
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
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
          have b4e37 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y y) := by
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
          have b4e39 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e36
            | exact resolve b4e36 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e42 : y = (σ y) := by
            first
            | (have i₁ := b4e40 x
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e40
            | exact resolve b4e40 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (M.op (σ X0) (σ X0)) (σ X0)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X2 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X1)) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X0 X0
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X2 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e57 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e61 : ∀ X0 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = y ∨ X0 = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e59 X0 x X2
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e59
            | (have j0 := b4e59 X0 x X2
               grind)
            | exact resolve b4e59 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e56 X0 X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e56
            | (have j0 := b4e56 X0 X1
               grind)
            | exact resolve b4e56 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e71 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (M.op X1 X1)
               have i₂ := b4e39 X1
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X1 : G, y = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e71 x X1
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e71
            | exact resolve b4e71 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e156 : ∀ X0 : G, y = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e39 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e39
            | exact resolve b4e39 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e977 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ y = (M.op X0 y) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e61 X0 X1
               grind)
            | exact superpose b4e61 b4e39
            | (have j1 := b4e61 X0 X1
               grind)
            | exact resolve b4e39 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e61
          have b4e1103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e60 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e1105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e1103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1103
          have b4e1213 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e63 x y
               grind)
            | exact superpose b4e63 b4e20
            | (have j1 := b4e63 x (M.op x x)
               grind)
            | exact resolve b4e20 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e1253 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e1213
               have r₂ := b4e23
               grind)
            | exact resolve b4e1213 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1213
          have b4e2834 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e1105 y X0
               have i₂ := b4e72 y
               grind)
            | exact superpose b4e72 b4e1105
            | (have j0 := b4e1105 y X0
               grind)
            | exact resolve b4e1105 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e1105
          have b4e2863 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b4e2834 X0
               have j1 := b4e977 X0 y
               grind)
            | (have r₁ := b4e2834 X0
               have r₂ := b4e977 X0 x
               grind)
            | (have r₁ := b4e2834 X0
               have r₂ := b4e977 y (M.op X0 y)
               grind)
            | (have r₁ := b4e2834 X0
               have r₂ := b4e977 (M.op X0 y) y
               grind)
            | exact resolve b4e2834 b4e977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e977 b4e2834
          have b4e2907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e1253
               have i₂ := b4e2863 x
               grind)
            | exact superpose b4e2863 b4e1253
            | (have j1 := b4e2863 x
               grind)
            | exact resolve b4e1253 b4e2863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1253 b4e2863
          have b4e2914 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
          clear b4e2907
          have b4e2921 : (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e2914
               have r₂ := b4e21
               grind)
            | exact resolve b4e2914 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2914
          have b4e3007 : y = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e156 x
               have i₂ := b4e2921
               grind)
            | exact superpose b4e2921 b4e156
            | exact resolve b4e156 b4e2921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156
          have b4e3008 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e2921
               grind)
            | exact superpose b4e2921 b4e14
            | exact resolve b4e14 b4e2921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2921
          have b4e3045 : x = (M.op x x) := by
            first
            | (have i₁ := b4e3008
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e3008
            | exact resolve b4e3008 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3008
          have b4e3046 : y = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e3007
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e3007
            | exact resolve b4e3007 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e3007
          have b4e3051 : y = (σ x) := by
            first
            | (have i₁ := b4e3046
               have i₂ := b4e3045
               grind)
            | exact superpose b4e3045 b4e3046
            | exact resolve b4e3046 b4e3045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3045 b4e3046
          have b4e3162 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e3051
               grind)
            | exact superpose b4e3051 b4e23
            | exact resolve b4e23 b4e3051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3051
          have b4e3197 : False := by grind
          exact b4e3197
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b5e100 : (σ y) ≠ (σ (M.op y y)) := by
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
          have b5e109 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e100
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e100
            | exact resolve b5e100 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100
          have b5e110 : False := by grind
          exact b5e110
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
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
          have b7e34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
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
          have b7e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e34 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op X1 X1)
               have i₂ := b7e38 X1
               grind)
            | exact superpose b7e38 b7e13
            | exact resolve b7e13 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) := by
            intro X1
            first
            | (have i₁ := b7e43 x X1
               have i₂ := b7e38 x
               grind)
            | exact superpose b7e38 b7e43
            | exact resolve b7e43 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e43
          have b7e107 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e44 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e44
            | exact resolve b7e44 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e44
          have b7e119 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e107
               grind)
            | exact superpose b7e107 b7e14
            | exact resolve b7e14 b7e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e120 : y = (M.op y y) := by
            first
            | (have i₁ := b7e119
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e119
            | exact resolve b7e119 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119
          have b7e124 : False := by grind
          exact b7e124
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
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
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
          have b8e32 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X4) X3) := by
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
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op X3 X3)
               have i₂ := b8e13 X3 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op X2 X3) X2
               have i₂ := b8e13 X0 X2 X3
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
          have b8e40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X0) (σ X0)) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e61 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ y) (σ y)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b8e61 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e56 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e56
            | (have j0 := b8e56 X0 X1
               grind)
            | exact resolve b8e56 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e70 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
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
          clear b8e30
          have b8e113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32 X1 (M.op X1 X1) X2 X3
               have i₂ := b8e35 X1 X0
               grind)
            | (have i₁ := b8e32 X1 (M.op X1 X1) X2 X3
               have i₂ := b8e35 X0 X1
               grind)
            | exact superpose b8e35 b8e32
            | exact resolve b8e32 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e195 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e40 X0 y
               have i₂ := b8e62 X0
               grind)
            | exact superpose b8e62 b8e40
            | (have j1 := b8e62 X0
               grind)
            | exact resolve b8e40 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e62
          have b8e264 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X2)) = (M.op (M.op (M.op X4 X5) X4) X6) := by
            intro X0 X1 X2 X4 X5 X6
            first
            | (have i₁ := b8e33 X4 X5 x X6
               have i₂ := b8e34 X0 x X1 X2
               grind)
            | (have i₁ := b8e33 X0 X1 (M.op X0 (M.op X0 X0)) x
               have i₂ := b8e34 X0 X1 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b8e34 b8e33
            | exact resolve b8e33 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e34
          have b8e708 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e64 x y
               grind)
            | exact superpose b8e64 b8e20
            | (have j1 := b8e64 x (M.op x x)
               grind)
            | exact resolve b8e20 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e738 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e708
               have r₂ := b8e23
               grind)
            | exact resolve b8e708 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e708
          have b8e2316 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (k (τ (σ (M.op y y))) y) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e195 (σ (M.op y y))
               have i₂ := b8e73 y X0 X1
               grind)
            | exact superpose b8e73 b8e195
            | (have j0 := b8e195 (σ (M.op y y))
               grind)
            | exact resolve b8e195 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73 b8e195
          have b8e2353 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (k (τ (σ (M.op y y))) y) := by
            intro X0 X1
            first
            | (have j0 := b8e2316 X0 X1
               grind)
            | (have r₁ := b8e2316 X0 X1
               have r₂ := b8e70
               grind)
            | exact resolve b8e2316 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70 b8e2316
          have b8e2366 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X0)) = (k (M.op y y) y) := by
            intro X0 X1
            first
            | (have i₁ := b8e2353 X0 X1
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e2353
            | exact resolve b8e2353 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2353
          have b8e2724 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ (k (M.op y y) y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e15 (M.op (M.op X0 X1) X0)
               have i₂ := b8e2366 X0 X1
               grind)
            | exact superpose b8e2366 b8e15
            | exact resolve b8e15 b8e2366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3518 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b8e2724 X0 X1
               have i₂ := b8e18 (M.op y y) y
               grind)
            | exact superpose b8e18 b8e2724
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | exact resolve b8e2724 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3532 : ∀ X2 X3 : G, (M.op (M.op X2 (M.op X2 X2)) X3) = (σ (k (M.op y y) y)) := by
            intro X2 X3
            first
            | (have i₁ := b8e113 X2 X3 x x
               have i₂ := b8e2724 x x
               grind)
            | exact superpose b8e2724 b8e113
            | exact resolve b8e113 b8e2724
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113 b8e2724
          have b8e3592 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) := by
            intro X0 X1
            first
            | (have j0 := b8e3518 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3518
          have b8e3599 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ (M.op y (M.op y y))) := by
            intro X0 X1
            first
            | (have j0 := b8e3592 X0 X1
               grind)
            | (have r₁ := b8e3592 X0 X1
               have r₂ := b8e22
               grind)
            | exact resolve b8e3592 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3592
          have b8e4624 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3599 X1 X2
               have i₂ := b8e35 y X0
               grind)
            | (have i₁ := b8e3599 X1 X2
               have i₂ := b8e35 X0 y
               grind)
            | exact superpose b8e35 b8e3599
            | exact resolve b8e3599 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e4645 : (k (M.op y y) y) = (τ (σ (M.op y (M.op y y)))) := by
            first
            | (have i₁ := b8e2366 x x
               have i₂ := b8e3599 x x
               grind)
            | exact superpose b8e3599 b8e2366
            | exact resolve b8e2366 b8e3599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2366 b8e3599
          have b8e4726 : (k (M.op y y) y) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b8e4645
               have i₂ := b8e14 (M.op y (M.op y y))
               grind)
            | exact superpose b8e14 b8e4645
            | exact resolve b8e4645 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4645
          have b8e6878 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e738
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e738
            | (have j1 := b8e18 (M.op x x) x
               grind)
            | (have r₁ := b8e738
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e738
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e738 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e738
          have b8e6879 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b8e6878
          have b8e6881 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b8e6879
               have r₂ := b8e21
               grind)
            | exact resolve b8e6879 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6879
          have b8e8298 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e6881
               grind)
            | exact superpose b8e6881 b8e14
            | exact resolve b8e14 b8e6881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6881
          have b8e8336 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e8298
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e8298
            | exact resolve b8e8298 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8298
          have b8e8337 : x = (M.op x x) := by grind
          clear b8e8336
          have b8e9109 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ (M.op x x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e4624 x X0 X1
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e4624
            | exact resolve b8e4624 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4624
          have b8e9110 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e13
            | exact resolve b8e13 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e9112 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x x) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 x x
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e32
            | exact resolve b8e32 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e9140 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e9112 X0 X1
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e9112
            | exact resolve b8e9112 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9112
          have b8e9142 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e9110 X0
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e9110
            | exact resolve b8e9110 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9110
          have b8e9143 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e9109 X0 X1
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e9109
            | exact resolve b8e9109 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9109
          have b8e9163 : x = (σ x) := by
            first
            | (have i₁ := b8e9143 x x
               have i₂ := b8e9140 x x
               grind)
            | exact superpose b8e9140 b8e9143
            | exact resolve b8e9143 b8e9140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9140 b8e9143
          have b8e9945 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e9163
               grind)
            | exact superpose b8e9163 b8e20
            | exact resolve b8e20 b8e9163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11029 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X2)) = (M.op (M.op x x) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e264 X0 X1 X2 x x X3
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e264
            | exact resolve b8e264 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e264
          have b8e11471 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X2)) = (M.op x X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e11029 X0 X1 X2 X3
               have i₂ := b8e8337
               grind)
            | exact superpose b8e8337 b8e11029
            | exact resolve b8e11029 b8e8337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8337 b8e11029
          have b8e11573 : ∀ X3 : G, (σ (k (M.op y y) y)) = (M.op x X3) := by
            intro X3
            first
            | (have i₁ := b8e11471 x x x X3
               have i₂ := b8e3532 x (M.op x x)
               grind)
            | exact superpose b8e3532 b8e11471
            | exact resolve b8e11471 b8e3532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3532 b8e11471
          have b8e11662 : ∀ X3 : G, (σ (M.op y (M.op y y))) = (M.op x X3) := by
            intro X3
            first
            | (have i₁ := b8e11573 X3
               have i₂ := b8e4726
               grind)
            | exact superpose b8e4726 b8e11573
            | exact resolve b8e11573 b8e4726
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4726 b8e11573
          have b8e11731 : ∀ X3 : G, (σ x) = (M.op x X3) := by
            intro X3
            first
            | (have i₁ := b8e11662 X3
               have i₂ := b8e9142 y
               grind)
            | exact superpose b8e9142 b8e11662
            | exact resolve b8e11662 b8e9142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9142 b8e11662
          have b8e11776 : ∀ X3 : G, x = (M.op x X3) := by
            intro X3
            first
            | (have i₁ := b8e11731 X3
               have i₂ := b8e9163
               grind)
            | exact superpose b8e9163 b8e11731
            | exact resolve b8e11731 b8e9163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11731
          have b8e31166 : (σ x) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e9945
               have i₂ := b8e11776 y
               grind)
            | exact superpose b8e11776 b8e9945
            | exact resolve b8e9945 b8e11776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9945
          have b8e31167 : x ≠ (σ x) := by
            first
            | (have i₁ := b8e31166
               have i₂ := b8e11776 (σ y)
               grind)
            | exact superpose b8e11776 b8e31166
            | exact resolve b8e31166 b8e11776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11776 b8e31166
          have b8e31168 : False := by grind
          exact b8e31168

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4400 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4400 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
      have b0e37 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
      have b0e38 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
      have b0e40 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1
        grind
      have b0e43 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op y (M.op x y)) := by
        intro X1
        first
        | (have i₁ := b0e11 y x x
           have i₂ := b0e38 x
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) := by
        intro X1
        first
        | (have i₁ := b0e43 X1
           have i₂ := b0e38 (M.op x y)
           grind)
        | exact superpose b0e38 b0e43
        | exact resolve b0e43 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e45 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e44 x
           have i₂ := b0e11 x y x
           grind)
        | exact superpose b0e11 b0e44
        | exact resolve b0e44 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e78 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e81 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X1
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e37
        | exact resolve b0e37 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e150 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) := by
        intro X0
        grind
      clear b0e81
      have b0e254 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e40 x y
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e40
        | exact resolve b0e40 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e45
      have b0e533 : ∀ X0 : G, (k y (τ (M.op (σ y) X0))) = (τ (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e78 y (M.op (σ y) X0)
           have i₂ := b0e150 X0
           grind)
        | exact superpose b0e150 b0e78
        | exact resolve b0e78 b0e150
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78 b0e150
      have b0e535 : ∀ X0 : G, y = (k y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e533 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e533
        | exact resolve b0e533 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e533
      have b0e694 : ∀ X0 : G, y = (M.op y (τ (M.op (σ y) X0))) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e16 y (τ (M.op (σ y) X0))
           have i₂ := b0e535 X0
           grind)
        | exact superpose b0e535 b0e16
        | (have j0 := b0e16 y (τ (M.op (σ y) X0))
           grind)
        | exact resolve b0e16 b0e535
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e535
      have b0e695 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e694 X0
           have i₂ := b0e38 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e38 b0e694
        | (have j0 := b0e694 X0
           grind)
        | exact resolve b0e694 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e694
      have b0e701 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e695 X0
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e695
        | (have j0 := b0e695 X0
           grind)
        | exact resolve b0e695 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e695
      have b0e705 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e701 X0
           have i₂ := b0e38 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e38 b0e701
        | (have j0 := b0e701 X0
           grind)
        | exact resolve b0e701 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e701
      have b0e706 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have j0 := b0e705 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e705
      have b0e1086 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e59 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e1088 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e1086 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1086
      have b0e5373 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op (σ y) X0)
           have i₂ := b0e706 X0
           grind)
        | exact superpose b0e706 b0e13
        | exact resolve b0e13 b0e706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e706
      have b0e5381 : y = (M.op x y) := by
        first
        | (have r₁ := b0e5373 x
           have r₂ := b0e84 x
           grind)
        | exact resolve b0e5373 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5373
      have b0e5442 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e84 X0
           have i₂ := b0e5381
           grind)
        | exact superpose b0e5381 b0e84
        | exact resolve b0e84 b0e5381
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84
      have b0e5443 : y = (k y y) := by
        first
        | (have i₁ := b0e254
           have i₂ := b0e5381
           grind)
        | exact superpose b0e5381 b0e254
        | exact resolve b0e254 b0e5381
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254 b0e5381
      have b0e5619 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e1088 y
           have i₂ := b0e5443
           grind)
        | exact superpose b0e5443 b0e1088
        | (have j0 := b0e1088 y
           grind)
        | exact resolve b0e1088 b0e5443
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1088 b0e5443
      have b0e5625 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e5619
      have b0e5631 : False := by grind
      exact b0e5631
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
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
        have b1e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
        have b1e36 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e32 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e32
          | exact resolve b1e32 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e53 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e36
        have b1e60 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e90 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e60
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e60 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e94 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e90
        have b1e98 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e94
             have i₂ := b1e33 y
             grind)
          | exact superpose b1e33 b1e94
          | exact resolve b1e94 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94
        have b1e99 : y = (M.op y y) := by
          first
          | (have r₁ := b1e98
             have r₂ := b1e24
             grind)
          | exact resolve b1e98 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e98
        have b1e100 : y = (M.op x y) := by
          first
          | (have i₁ := b1e99
             have i₂ := b1e33 y
             grind)
          | exact superpose b1e33 b1e99
          | exact resolve b1e99 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e99
        have b1e153 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e100
             grind)
          | exact superpose b1e100 b1e24
          | exact resolve b1e24 b1e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e100
        have b1e158 : False := by grind
        exact b1e158
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
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
        have b2e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e222 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e75
        have b2e235 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e222 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e222
          | exact resolve b2e222 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e222
        have b2e601 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e57 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e602 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e601
             have r₂ := b2e22
             grind)
          | exact resolve b2e601 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e601
        have b2e603 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e602
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e602
          | exact resolve b2e602 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e602
        have b2e604 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e603
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e603
          | exact resolve b2e603 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e603
        have b2e608 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e604
             grind)
          | exact superpose b2e604 b2e22
          | exact resolve b2e22 b2e604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e611 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e27 (σ x) (σ y) x x
             have i₂ := b2e604
             grind)
          | exact superpose b2e604 b2e27
          | exact resolve b2e27 b2e604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e938 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e604
             have i₂ := b2e611 (σ y) X0
             grind)
          | (have i₁ := b2e604
             have i₂ := b2e611 X0 (σ y)
             grind)
          | exact superpose b2e611 b2e604
          | exact resolve b2e604 b2e611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e604 b2e611
        have b2e1053 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e235 x
             have i₂ := b2e938 (σ x)
             grind)
          | exact superpose b2e938 b2e235
          | exact resolve b2e235 b2e938
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e235 b2e938
        have b2e1084 : x = (k x x) := by
          first
          | (have i₁ := b2e1053
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1053
          | exact resolve b2e1053 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1053
        have b2e1124 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e1084
             grind)
          | exact superpose b2e1084 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e1084
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1084
        have b2e1125 : x = (M.op x x) := by grind
        clear b2e1124
        have b2e1183 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e1125
             grind)
          | exact superpose b2e1125 b2e20
          | exact resolve b2e20 b2e1125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1125
        have b2e1352 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e608
             have i₂ := b2e1183
             grind)
          | exact superpose b2e1183 b2e608
          | exact resolve b2e608 b2e1183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e608 b2e1183
        have b2e1354 : False := by grind
        exact b2e1354
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e46 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e46 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e46
          | exact resolve b3e46 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e1023 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e68 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e68
          | exact resolve b3e68 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e1118 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e1023
        have b3e1586 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e1118
             grind)
          | exact superpose b3e1118 b3e13
          | exact resolve b3e13 b3e1118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1603 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1586
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1586
          | exact resolve b3e1586 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1586
        have b3e1619 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e1603
             grind)
          | exact superpose b3e1603 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e1603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1603
        have b3e1620 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e1619
        have b3e1622 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e1620
             have r₂ := b3e20
             grind)
          | exact resolve b3e1620 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1620
        have b3e1687 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e1622
        have b3e1796 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1118
             have i₂ := b3e1687
             grind)
          | exact superpose b3e1687 b3e1118
          | exact resolve b3e1118 b3e1687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1118 b3e1687
        have b3e1805 : (σ x) = (σ y) := by grind
        clear b3e1796
        have b3e1997 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1805
             grind)
          | exact superpose b3e1805 b3e13
          | exact resolve b3e13 b3e1805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1805
        have b3e2013 : x = y := by
          first
          | (have i₁ := b3e1997
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1997
          | exact resolve b3e1997 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1997
        have b3e2157 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e49 X0
             have i₂ := b3e2013
             grind)
          | exact superpose b3e2013 b3e49
          | exact resolve b3e49 b3e2013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e2299 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e2157 x
             grind)
          | exact superpose b3e2157 b3e20
          | exact resolve b3e20 b3e2157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2157
        have b3e2335 : False := by grind
        exact b3e2335
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e51 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e49
          have b5e53 : x = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e77 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e199 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e77
          have b5e212 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e199 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e199
            | exact resolve b5e199 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e737 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e738 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e737
               have r₂ := b5e24
               grind)
            | exact resolve b5e737 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e737
          have b5e739 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e738
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e738
            | exact resolve b5e738 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e738
          have b5e740 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e739
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e739
            | exact resolve b5e739 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e739
          have b5e746 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 (σ x) (σ y) x x
               have i₂ := b5e740
               grind)
            | exact superpose b5e740 b5e35
            | exact resolve b5e35 b5e740
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1091 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e740
               have i₂ := b5e746 (σ y) X0
               grind)
            | (have i₁ := b5e740
               have i₂ := b5e746 X0 (σ y)
               grind)
            | exact superpose b5e746 b5e740
            | exact resolve b5e740 b5e746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e740 b5e746
          have b5e1206 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b5e212 x
               have i₂ := b5e1091 (σ x)
               grind)
            | exact superpose b5e1091 b5e212
            | exact resolve b5e212 b5e1091
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e212 b5e1091
          have b5e1239 : x = (k x x) := by
            first
            | (have i₁ := b5e1206
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1206
            | exact resolve b5e1206 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1206
          have b5e1363 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e1239
               grind)
            | exact superpose b5e1239 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e1239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1239
          have b5e1364 : x = (M.op x x) := by grind
          clear b5e1363
          have b5e1470 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 x x x x
               have i₂ := b5e1364
               grind)
            | exact superpose b5e1364 b5e35
            | exact resolve b5e35 b5e1364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e1364
          have b5e1812 : ∀ X0 : G, y ≠ (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e1470 x X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e1470 X0 x
               grind)
            | exact superpose b5e1470 b5e21
            | exact resolve b5e21 b5e1470
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1813 : ∀ X0 : G, y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e1470 y X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e1470 X0 y
               grind)
            | exact superpose b5e1470 b5e22
            | exact resolve b5e22 b5e1470
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1470
          have b5e1839 : False := by grind
          exact b5e1839
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
        have b6e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e81 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e90 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e81
             have r₂ := b6e20
             grind)
          | exact resolve b6e81 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e93 : x = (M.op x y) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e21
             grind)
          | exact resolve b6e90 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e95 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e21
          | exact resolve b6e21 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e97 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e12 x y x
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e12
          | exact resolve b6e12 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e233 : x = (M.op x x) := by
          first
          | (have i₁ := b6e93
             have i₂ := b6e97 y
             grind)
          | exact superpose b6e97 b6e93
          | exact resolve b6e93 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93 b6e97
        have b6e428 : x = (k x x) := by grind
        clear b6e233
        have b6e950 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e79 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e79
          | exact resolve b6e79 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e1031 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e950
        have b6e1059 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1031
             have i₂ := b6e428
             grind)
          | exact superpose b6e428 b6e1031
          | exact resolve b6e1031 b6e428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e428 b6e1031
        have b6e1060 : (σ x) = (σ y) := by grind
        clear b6e1059
        have b6e1101 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1060
             grind)
          | exact superpose b6e1060 b6e13
          | exact resolve b6e13 b6e1060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1060
        have b6e1111 : x = y := by
          first
          | (have i₁ := b6e1101
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1101
          | exact resolve b6e1101 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1101
        have b6e1116 : False := by grind
        exact b6e1116
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e53 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e53
            | exact resolve b7e53 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
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
          have b7e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e82 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
          have b7e83 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e21
               grind)
            | exact resolve b7e82 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e85 : x = (M.op x y) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e22
               grind)
            | exact resolve b7e83 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e97 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e13 x y x
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e13
            | exact resolve b7e13 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e591 : x = (M.op x x) := by
            first
            | (have i₁ := b7e85
               have i₂ := b7e97 y
               grind)
            | exact superpose b7e97 b7e85
            | exact resolve b7e85 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e97
          have b7e651 : x = (k x x) := by grind
          clear b7e591
          have b7e873 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e65 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e875 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e873 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e873
          have b7e4010 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e875 x
               have i₂ := b7e651
               grind)
            | exact superpose b7e651 b7e875
            | (have j0 := b7e875 x
               grind)
            | exact resolve b7e875 b7e651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e651 b7e875
          have b7e4018 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e4010
          have b7e4087 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e29 (σ x) (σ x) x x
               have i₂ := b7e4018
               grind)
            | exact superpose b7e4018 b7e29
            | exact resolve b7e29 b7e4018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e4018
          have b7e4215 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e4087 (σ x) X0
               grind)
            | (have i₁ := b7e23
               have i₂ := b7e4087 X0 (σ x)
               grind)
            | exact superpose b7e4087 b7e23
            | exact resolve b7e23 b7e4087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e4216 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e4087 (σ y) X0
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e4087 X0 (σ y)
               grind)
            | exact superpose b7e4087 b7e24
            | exact resolve b7e24 b7e4087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4087
          have b7e4258 : False := by grind
          exact b7e4258
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
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e736 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e737 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e736
               have r₂ := b8e24
               grind)
            | exact resolve b8e736 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e736
          have b8e738 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e737
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e737
            | exact resolve b8e737 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e737
          have b8e741 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e738
               grind)
            | exact superpose b8e738 b8e20
            | exact resolve b8e20 b8e738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e738
          have b8e1036 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e741
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e741
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e741 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e741
          have b8e1037 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1036
          have b8e1040 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1037
               have r₂ := b8e21
               grind)
            | exact resolve b8e1037 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1037
          have b8e1043 : False := by grind
          exact b8e1043

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pyx_Equation4401 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e63 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e66 : False := by grind
      exact b0e66
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 X0 (M.op X0 x) X3
               have i₂ := b5e13 X0 x X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 X0 x X3
               have i₂ := b5e13 X0 x X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y x) := by
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
          have b5e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e13 X0 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b5e43 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e43
            | exact resolve b5e43 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e56 : y = (M.op y x) := by
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
          have b5e57 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e61 : x = y ∨ x = (k x y) := by grind
          clear b5e57
          have b5e63 : x = (k x y) := by
            first
            | (have r₁ := b5e61
               have r₂ := b5e21
               grind)
            | exact resolve b5e61 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e70 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e13
            | exact resolve b5e13 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e96 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e131 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b5e42 y X0 x
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e42
            | exact resolve b5e42 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e185 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e46 (σ X0) X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e46
            | exact resolve b5e46 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e893 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e66 y x
               grind)
            | exact superpose b5e66 b5e24
            | (have j1 := b5e66 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e66 y x
               grind)
            | exact resolve b5e24 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e916 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b5e893
          have b5e922 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e916
               have r₂ := b5e23
               grind)
            | exact resolve b5e916 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e916
          have b5e934 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e922
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e922
            | exact resolve b5e922 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e922
          have b5e946 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e42 (σ y) X0 (σ x)
               have i₂ := b5e934
               grind)
            | exact superpose b5e934 b5e42
            | exact resolve b5e42 b5e934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e951 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e46 (σ y) X0 (σ x)
               have i₂ := b5e934
               grind)
            | exact superpose b5e934 b5e46
            | exact resolve b5e46 b5e934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e956 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e951 x
               have i₂ := b5e185 y x
               grind)
            | exact superpose b5e185 b5e951
            | exact resolve b5e951 b5e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e185 b5e951
          have b5e961 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e946 x
               have i₂ := b5e97 y x
               grind)
            | exact superpose b5e97 b5e946
            | exact resolve b5e946 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e946
          have b5e969 : (σ x) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e956
               have i₂ := b5e934
               grind)
            | exact superpose b5e934 b5e956
            | exact resolve b5e956 b5e934
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e934 b5e956
          have b5e1374 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) X0) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e40 (σ y) X0 (σ (M.op y y))
               have i₂ := b5e969
               grind)
            | exact superpose b5e969 b5e40
            | exact resolve b5e40 b5e969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e1400 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
            first
            | (have i₁ := b5e1374 x
               have i₂ := b5e97 y x
               grind)
            | exact superpose b5e97 b5e1374
            | exact resolve b5e1374 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1374
          have b5e1410 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b5e1400
               have i₂ := b5e96 y (σ (M.op y y))
               grind)
            | exact superpose b5e96 b5e1400
            | exact resolve b5e1400 b5e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96 b5e1400
          have b5e1848 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e97 y (σ (M.op y y))
               have i₂ := b5e969
               grind)
            | exact superpose b5e969 b5e97
            | exact resolve b5e97 b5e969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97 b5e969
          have b5e2893 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ (M.op y y))) = (σ (k (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e66 y (M.op y y)
               have i₂ := b5e1410
               grind)
            | exact superpose b5e1410 b5e66
            | (have j0 := b5e66 y (M.op y y)
               grind)
            | exact resolve b5e66 b5e1410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e2937 : (M.op (σ y) (σ (M.op y y))) = (σ (k (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e2893
               have r₂ := b5e24
               grind)
            | exact resolve b5e2893 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2893
          have b5e2952 : (M.op (σ x) (σ y)) = (σ (k (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e2937
               have i₂ := b5e961
               grind)
            | exact superpose b5e961 b5e2937
            | exact resolve b5e2937 b5e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e961 b5e2937
          have b5e2962 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e2952
               have i₂ := b5e1848
               grind)
            | exact superpose b5e1848 b5e2952
            | exact resolve b5e2952 b5e1848
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1848 b5e2952
          have b5e17553 : (k (M.op y y) y) = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e14 (k (M.op y y) y)
               have i₂ := b5e2962
               grind)
            | exact superpose b5e2962 b5e14
            | exact resolve b5e14 b5e2962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2962
          have b5e17605 : x = (k (M.op y y) y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e17553
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e17553
            | exact resolve b5e17553 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17553
          have b5e17684 : x = (M.op y (M.op y y)) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e18 (M.op y y) y
               have i₂ := b5e17605
               grind)
            | exact superpose b5e17605 b5e18
            | (have j0 := b5e18 (M.op y y) y
               grind)
            | exact resolve b5e18 b5e17605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17605
          have b5e17685 : x = (M.op y y) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e17684
               have i₂ := b5e70 y
               grind)
            | exact superpose b5e70 b5e17684
            | exact resolve b5e17684 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17684
          have b5e17687 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e17685
               have i₂ := b5e131 y
               grind)
            | exact superpose b5e131 b5e17685
            | exact resolve b5e17685 b5e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131 b5e17685
          have b5e17688 : (σ y) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b5e17687
          have b5e31851 : (M.op y y) = (τ (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e17688
               grind)
            | exact superpose b5e17688 b5e14
            | exact resolve b5e14 b5e17688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17688
          have b5e31905 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e31851
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e31851
            | exact resolve b5e31851 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31851
          have b5e31906 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b5e31905
          have b5e32856 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e46 y X0 y
               have i₂ := b5e31906
               grind)
            | exact superpose b5e31906 b5e46
            | exact resolve b5e46 b5e31906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e31906
          have b5e32996 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e32856 x
               have i₂ := b5e70 x
               grind)
            | exact superpose b5e70 b5e32856
            | exact resolve b5e32856 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e32856
          have b5e33064 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e32996
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e32996
            | exact resolve b5e32996 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e32996
          have b5e33065 : y = (M.op y y) := by grind
          clear b5e33064
          have b5e33374 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1410
               have i₂ := b5e33065
               grind)
            | exact superpose b5e33065 b5e1410
            | exact resolve b5e1410 b5e33065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1410
          have b5e33482 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e33374
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e33374
            | exact resolve b5e33374 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e33374
          have b5e33490 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e33482
               have i₂ := b5e33065
               grind)
            | exact superpose b5e33065 b5e33482
            | exact resolve b5e33482 b5e33065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33065 b5e33482
          have b5e33496 : False := by grind
          exact b5e33496
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
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
          have b7e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e13 X0 (M.op X0 x) X3
               have i₂ := b7e13 X0 x X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e13 X0 x X3
               have i₂ := b7e13 X0 x X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 x
               have i₂ := b7e13 X0 X2 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ x)) := by
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
          have b7e49 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e52 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e49
          have b7e53 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e52
               have r₂ := b7e23
               grind)
            | exact resolve b7e52 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e54 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e53
            | exact resolve b7e53 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
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
          have b7e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b7e68 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e69 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : x = (M.op y x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e94 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ X0) (σ X0) X1
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e98 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e41 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e41
            | exact resolve b7e41 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : (σ y) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b7e41 (σ x)
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e41
            | exact resolve b7e41 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e134 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) := by
            intro X0
            first
            | (have i₁ := b7e36 y X0 x
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e36
            | exact resolve b7e36 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e155 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ x) X0
               have i₂ := b7e98
               grind)
            | exact superpose b7e98 b7e13
            | exact resolve b7e13 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e156 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e155 X0
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e155
            | exact resolve b7e155 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e155
          have b7e160 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b7e156 x
               have i₂ := b7e94 y x
               grind)
            | exact superpose b7e94 b7e156
            | exact resolve b7e156 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e156
          have b7e187 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e40 y X0 x
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e40
            | exact resolve b7e40 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e205 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e187 X0
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e187
            | exact resolve b7e187 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e187
          have b7e220 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) y)) := by
            intro X0
            first
            | (have i₁ := b7e205 (M.op y x)
               have i₂ := b7e13 y x X0
               grind)
            | exact superpose b7e13 b7e205
            | exact resolve b7e205 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e237 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b7e220 x
               have i₂ := b7e134 x
               grind)
            | exact superpose b7e134 b7e220
            | exact resolve b7e220 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e220
          have b7e242 : ∀ X1 : G, (M.op x y) = (M.op y (M.op (M.op y X1) y)) := by
            intro X1
            first
            | (have i₁ := b7e34 y X1 (M.op y x)
               have i₂ := b7e205 x
               grind)
            | exact superpose b7e205 b7e34
            | exact resolve b7e34 b7e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e205
          have b7e298 : (M.op x y) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b7e242 x
               have i₂ := b7e134 x
               grind)
            | exact superpose b7e134 b7e242
            | exact resolve b7e242 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e242
          have b7e301 : x = (M.op x y) := by
            first
            | (have i₁ := b7e298
               have i₂ := b7e237
               grind)
            | exact superpose b7e237 b7e298
            | exact resolve b7e298 b7e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e237 b7e298
          have b7e308 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b7e36 x X0 y
               have i₂ := b7e301
               grind)
            | exact superpose b7e301 b7e36
            | exact resolve b7e36 b7e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e310 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e40 x X0 y
               have i₂ := b7e301
               grind)
            | exact superpose b7e301 b7e40
            | exact resolve b7e40 b7e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e312 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e37 (σ x)
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e37
            | exact resolve b7e37 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e349 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e312
               have i₂ := b7e98
               grind)
            | exact superpose b7e98 b7e312
            | exact resolve b7e312 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e312
          have b7e700 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X0 (M.op (M.op X0 X1) X0))) = (M.op (M.op X0 (M.op X0 X3)) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e39 X0 X3 X2 X0
               have i₂ := b7e34 X0 X1 X2
               grind)
            | exact superpose b7e34 b7e39
            | exact resolve b7e39 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e741 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op (M.op x x) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 x y X0 X1
               have i₂ := b7e301
               grind)
            | exact superpose b7e301 b7e39
            | exact resolve b7e39 b7e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e1004 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op x X0)) = (M.op (M.op x X0) (M.op (M.op x x) (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 (M.op x X0) x X1
               have i₂ := b7e308 X0
               grind)
            | exact superpose b7e308 b7e34
            | exact resolve b7e34 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e1008 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op x X0)) = (M.op (M.op x x) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 (M.op x X0) X1 x
               have i₂ := b7e308 X0
               grind)
            | exact superpose b7e308 b7e36
            | exact resolve b7e36 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e1018 : ∀ X0 : G, (M.op (M.op x x) (M.op x X0)) = (M.op (M.op x X0) (M.op (M.op x x) (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b7e1004 X0 x
               have i₂ := b7e1008 X0 x
               grind)
            | exact superpose b7e1008 b7e1004
            | exact resolve b7e1004 b7e1008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1004
          have b7e1262 : (σ x) = (σ y) ∨ (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e62 x (M.op x x)
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e62
            | (have j0 := b7e62 x (M.op x x)
               grind)
            | exact resolve b7e62 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e99
          have b7e1285 : (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b7e1262
               have r₂ := b7e23
               grind)
            | exact resolve b7e1262 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1262
          have b7e1290 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e1285
               have i₂ := b7e349
               grind)
            | exact superpose b7e349 b7e1285
            | exact resolve b7e1285 b7e349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1285
          have b7e20456 : (k (M.op x x) x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e14 (k (M.op x x) x)
               have i₂ := b7e1290
               grind)
            | exact superpose b7e1290 b7e14
            | exact resolve b7e14 b7e1290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1290
          have b7e20508 : y = (k (M.op x x) x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e20456
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e20456
            | exact resolve b7e20456 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20456
          have b7e20584 : y = (M.op x (M.op x x)) ∨ x = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e18 (M.op x x) x
               have i₂ := b7e20508
               grind)
            | exact superpose b7e20508 b7e18
            | (have j0 := b7e18 (M.op x x) x
               grind)
            | exact resolve b7e18 b7e20508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20508
          have b7e20585 : y = (M.op x x) ∨ x = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e20584
               have i₂ := b7e310 x
               grind)
            | exact superpose b7e310 b7e20584
            | exact resolve b7e20584 b7e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e310 b7e20584
          have b7e20587 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e20585
               have i₂ := b7e308 x
               grind)
            | exact superpose b7e308 b7e20585
            | exact resolve b7e20585 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20585
          have b7e20588 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e20587
          have b7e29258 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e20588
               grind)
            | exact superpose b7e20588 b7e14
            | exact resolve b7e14 b7e20588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20588
          have b7e29310 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e29258
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e29258
            | exact resolve b7e29258 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29258
          have b7e29311 : x = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b7e29310
          have b7e30486 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e349
               have i₂ := b7e29311
               grind)
            | exact superpose b7e29311 b7e349
            | exact resolve b7e349 b7e29311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e349 b7e29311
          have b7e30579 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e30486
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e30486
            | exact resolve b7e30486 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e30486
          have b7e31581 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e30579
               grind)
            | exact superpose b7e30579 b7e14
            | exact resolve b7e14 b7e30579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30579
          have b7e31635 : y = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e31581
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e31581
            | exact resolve b7e31581 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31581
          have b7e31636 : y = (M.op x x) := by grind
          clear b7e31635
          have b7e32062 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) (M.op (M.op x X0) X2)) (M.op x x)) = (M.op (M.op x x) (M.op (M.op x X0) (M.op (M.op (M.op x X0) X1) (M.op x X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e700 (M.op x X0) X1 x x
               have i₂ := b7e308 X0
               grind)
            | exact superpose b7e308 b7e700
            | exact resolve b7e700 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e308 b7e700
          have b7e32455 : ∀ X0 X2 : G, (M.op (M.op (M.op x X0) (M.op (M.op x X0) X2)) (M.op x x)) = (M.op (M.op x x) (M.op (M.op x X0) (M.op (M.op x x) (M.op x X0)))) := by
            intro X0 X2
            first
            | (have i₁ := b7e32062 X0 x X2
               have i₂ := b7e1008 X0 x
               grind)
            | exact superpose b7e1008 b7e32062
            | exact resolve b7e32062 b7e1008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1008 b7e32062
          have b7e32595 : ∀ X0 X2 : G, (M.op (M.op (M.op x X0) (M.op (M.op x X0) X2)) (M.op x x)) = (M.op (M.op x x) (M.op (M.op x x) (M.op x X0))) := by
            intro X0 X2
            first
            | (have i₁ := b7e32455 X0 X2
               have i₂ := b7e1018 X0
               grind)
            | exact superpose b7e1018 b7e32455
            | exact resolve b7e32455 b7e1018
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1018 b7e32455
          have b7e32694 : ∀ X0 X2 : G, (M.op (M.op (M.op x X0) (M.op (M.op x X0) X2)) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
            intro X0 X2
            first
            | (have i₁ := b7e32595 X0 X2
               have i₂ := b7e741 x (M.op x X0)
               grind)
            | exact superpose b7e741 b7e32595
            | exact resolve b7e32595 b7e741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32595
          have b7e32767 : ∀ X0 X2 : G, (M.op y y) = (M.op (M.op (M.op x X0) (M.op (M.op x X0) X2)) y) := by
            intro X0 X2
            first
            | (have i₁ := b7e32694 X0 X2
               have i₂ := b7e31636
               grind)
            | exact superpose b7e31636 b7e32694
            | exact resolve b7e32694 b7e31636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32694
          have b7e32814 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x x) (M.op x X0)) y) := by
            intro X0
            first
            | (have i₁ := b7e32767 X0 x
               have i₂ := b7e741 X0 x
               grind)
            | exact superpose b7e741 b7e32767
            | exact resolve b7e32767 b7e741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e741 b7e32767
          have b7e32837 : ∀ X0 : G, (M.op y y) = (M.op (M.op y (M.op x X0)) y) := by
            intro X0
            first
            | (have i₁ := b7e32814 X0
               have i₂ := b7e31636
               grind)
            | exact superpose b7e31636 b7e32814
            | exact resolve b7e32814 b7e31636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31636 b7e32814
          have b7e32851 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e32837 x
               have i₂ := b7e134 (M.op x x)
               grind)
            | exact superpose b7e134 b7e32837
            | exact resolve b7e32837 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134 b7e32837
          have b7e32860 : x = (M.op y y) := by
            first
            | (have i₁ := b7e32851
               have i₂ := b7e301
               grind)
            | exact superpose b7e301 b7e32851
            | exact resolve b7e32851 b7e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e301 b7e32851
          have b7e32870 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e160
               have i₂ := b7e32860
               grind)
            | exact superpose b7e32860 b7e160
            | exact resolve b7e160 b7e32860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e160 b7e32860
          have b7e33041 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e32870
               have i₂ := b7e98
               grind)
            | exact superpose b7e98 b7e32870
            | exact resolve b7e32870 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e32870
          have b7e33095 : False := by grind
          exact b7e33095
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
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
          have b8e60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e66 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) (σ X0) X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e120 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 (σ X0) X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e37
            | exact resolve b8e37 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e724 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e60 x y
               grind)
            | exact superpose b8e60 b8e20
            | (have j1 := b8e60 x y
               grind)
            | exact resolve b8e20 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e725 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e60 x y
               grind)
            | exact superpose b8e60 b8e24
            | (have j1 := b8e60 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e60 y x
               grind)
            | exact resolve b8e24 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e749 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e60 y x
               grind)
            | exact superpose b8e60 b8e24
            | (have j1 := b8e60 y x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e60 y x
               grind)
            | exact resolve b8e24 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e776 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b8e749
          have b8e782 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e776
               have r₂ := b8e23
               grind)
            | exact resolve b8e776 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e776
          have b8e786 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e725
               have r₂ := b8e23
               grind)
            | exact resolve b8e725 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e725
          have b8e787 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e724
               have r₂ := b8e23
               grind)
            | exact resolve b8e724 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e724
          have b8e796 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b8e786
               have i₂ := b8e782
               grind)
            | exact superpose b8e782 b8e786
            | exact resolve b8e786 b8e782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e786
          have b8e797 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b8e787
               have i₂ := b8e782
               grind)
            | exact superpose b8e782 b8e787
            | exact resolve b8e787 b8e782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e787
          have b8e814 : ∀ X0 : G, (M.op (σ y) (σ (k x y))) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e37 (σ y) X0 (σ x)
               have i₂ := b8e782
               grind)
            | exact superpose b8e782 b8e37
            | exact resolve b8e37 b8e782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e821 : (M.op (σ y) (σ (k x y))) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e814 x
               have i₂ := b8e120 y x
               grind)
            | exact superpose b8e120 b8e814
            | exact resolve b8e814 b8e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e120 b8e814
          have b8e2774 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e797
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e797
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e797
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e797
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e797 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e797
          have b8e2775 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = y := by grind
          clear b8e2774
          have b8e2776 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b8e2775
               have r₂ := b8e21
               grind)
            | exact resolve b8e2775 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2775
          have b8e2779 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e14 (k x y)
               have i₂ := b8e2776
               grind)
            | exact superpose b8e2776 b8e14
            | exact resolve b8e14 b8e2776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2776
          have b8e2823 : x = (k x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e2779
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e2779
            | exact resolve b8e2779 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2779
          have b8e3045 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e18 x y
               have i₂ := b8e2823
               grind)
            | exact superpose b8e2823 b8e18
            | (have j0 := b8e18 y x
               grind)
            | exact resolve b8e18 b8e2823
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2823
          have b8e3046 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e3045
          have b8e3049 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b8e3046
               have r₂ := b8e22
               grind)
            | exact resolve b8e3046 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3046
          have b8e3051 : x = (M.op y x) := by
            first
            | (have r₁ := b8e3049
               have r₂ := b8e21
               grind)
            | exact resolve b8e3049 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3049
          have b8e3281 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e3051
               grind)
            | exact superpose b8e3051 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3051
               grind)
            | exact resolve b8e17 b8e3051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3290 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e37 y X0 x
               have i₂ := b8e3051
               grind)
            | exact superpose b8e3051 b8e37
            | exact resolve b8e37 b8e3051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37
          have b8e3307 : x = y ∨ y = (k y x) := by grind
          clear b8e3281
          have b8e3313 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e3290 X0
               have i₂ := b8e3051
               grind)
            | exact superpose b8e3051 b8e3290
            | exact resolve b8e3290 b8e3051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3290
          have b8e3317 : y = (k y x) := by
            first
            | (have r₁ := b8e3307
               have r₂ := b8e21
               grind)
            | exact resolve b8e3307 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3307
          have b8e3557 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b8e796
               have i₂ := b8e3317
               grind)
            | exact superpose b8e3317 b8e796
            | exact resolve b8e796 b8e3317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e796 b8e3317
          have b8e3559 : (σ x) = (σ (k x y)) := by grind
          clear b8e3557
          have b8e4431 : ∀ X1 : G, x = (M.op (M.op y X1) y) := by
            intro X1
            first
            | (have i₁ := b8e13 y x X1
               have i₂ := b8e3313 x
               grind)
            | exact superpose b8e3313 b8e13
            | exact resolve b8e13 b8e3313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5718 : x = (M.op x y) := by
            first
            | (have i₁ := b8e4431 (M.op y x)
               have i₂ := b8e3313 x
               grind)
            | exact superpose b8e3313 b8e4431
            | exact resolve b8e4431 b8e3313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3313 b8e4431
          have b8e37444 : (M.op (σ y) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e821
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e821
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e821 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37445 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e821
               have i₂ := b8e3559
               grind)
            | exact superpose b8e3559 b8e821
            | exact resolve b8e821 b8e3559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e821
          have b8e37556 : (σ (k x y)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e37445
               have i₂ := b8e782
               grind)
            | exact superpose b8e782 b8e37445
            | exact resolve b8e37445 b8e782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e782 b8e37445
          have b8e37557 : (M.op (σ y) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y x))) ∨ x = y := by
            first
            | (have r₁ := b8e37444
               have r₂ := b8e22
               grind)
            | exact resolve b8e37444 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37444
          have b8e37560 : (σ x) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e37556
               have i₂ := b8e3559
               grind)
            | exact superpose b8e3559 b8e37556
            | exact resolve b8e37556 b8e3559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3559 b8e37556
          have b8e37561 : (M.op (σ y) (σ (M.op y y))) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have r₁ := b8e37557
               have r₂ := b8e21
               grind)
            | exact resolve b8e37557 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37557
          have b8e37564 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e37561
               have i₂ := b8e3051
               grind)
            | exact superpose b8e3051 b8e37561
            | exact resolve b8e37561 b8e3051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3051 b8e37561
          have b8e37566 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e37564
               have i₂ := b8e37560
               grind)
            | exact superpose b8e37560 b8e37564
            | exact resolve b8e37564 b8e37560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37564
          have b8e38713 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e66 y (σ x)
               have i₂ := b8e37566
               grind)
            | exact superpose b8e37566 b8e66
            | exact resolve b8e66 b8e37566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66 b8e37566
          have b8e38898 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e38713
               have i₂ := b8e37560
               grind)
            | exact superpose b8e37560 b8e38713
            | exact resolve b8e38713 b8e37560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37560 b8e38713
          have b8e40136 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e38898
               grind)
            | exact superpose b8e38898 b8e20
            | exact resolve b8e20 b8e38898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38898
          have b8e40286 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e40136
               have i₂ := b8e5718
               grind)
            | exact superpose b8e5718 b8e40136
            | exact resolve b8e40136 b8e5718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5718 b8e40136
          have b8e40287 : False := by grind
          exact b8e40287

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4404 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4404 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
        intro X0 X1 X2 X3
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
      have b0e35 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) (σ x) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 x X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e41 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e41
        | exact resolve b0e41 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op x X2) X3) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e11 x x X2 X3
           have i₂ := b0e41 x X0
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e394 : ∀ X0 X1 : G, (M.op x X1) = (k (M.op x X1) (M.op y X0)) := by
        intro X0 X1
        grind
      clear b0e52
      have b0e410 : ∀ X1 : G, (M.op x X1) = (k (M.op x X1) (M.op x y)) := by
        intro X1
        first
        | (have i₁ := b0e394 x X1
           have i₂ := b0e45 x
           grind)
        | exact superpose b0e45 b0e394
        | exact resolve b0e394 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e394
      have b0e436 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e35 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e35
        | exact resolve b0e35 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e506 : ∀ X0 X2 : G, (M.op (σ y) X0) = (M.op (σ y) X2) := by
        intro X0 X2
        first
        | (have i₁ := b0e40 x X2
           have i₂ := b0e40 x X0
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e581 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) := by
        intro X0
        grind
      clear b0e506
      have b0e1761 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e436 X0
           grind)
        | exact superpose b0e436 b0e18
        | exact resolve b0e18 b0e436
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e436
      have b0e2229 : ∀ X0 : G, (k y (τ (M.op (σ y) X0))) = (τ (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e134 y (M.op (σ y) X0)
           have i₂ := b0e581 X0
           grind)
        | exact superpose b0e581 b0e134
        | exact resolve b0e134 b0e581
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134 b0e581
      have b0e2232 : ∀ X0 : G, y = (k y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e2229 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e2229
        | exact resolve b0e2229 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2229
      have b0e2532 : ∀ X0 : G, y = (M.op y (τ (M.op (σ y) X0))) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e16 y (τ (M.op (σ y) X0))
           have i₂ := b0e2232 X0
           grind)
        | exact superpose b0e2232 b0e16
        | (have j0 := b0e16 y (τ (M.op (σ y) X0))
           grind)
        | exact resolve b0e16 b0e2232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2232
      have b0e2533 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e2532 X0
           have i₂ := b0e45 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e45 b0e2532
        | (have j0 := b0e2532 X0
           grind)
        | exact resolve b0e2532 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2532
      have b0e2544 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e2533 X0
           have i₂ := b0e45 y
           grind)
        | exact superpose b0e45 b0e2533
        | (have j0 := b0e2533 X0
           grind)
        | exact resolve b0e2533 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2533
      have b0e2551 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e2544 X0
           have i₂ := b0e45 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e45 b0e2544
        | (have j0 := b0e2544 X0
           grind)
        | exact resolve b0e2544 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e2544
      have b0e2552 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have j0 := b0e2551 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2551
      have b0e3387 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e85 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e3389 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e3387 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3387
      have b0e7916 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op (σ y) X0)
           have i₂ := b0e2552 X0
           grind)
        | exact superpose b0e2552 b0e13
        | exact resolve b0e13 b0e2552
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2552
      have b0e7924 : y = (M.op x y) := by
        first
        | (have r₁ := b0e7916 x
           have r₂ := b0e1761 x
           grind)
        | exact resolve b0e7916 b0e1761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7916
      have b0e8469 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e1761 X0
           have i₂ := b0e7924
           grind)
        | exact superpose b0e7924 b0e1761
        | exact resolve b0e1761 b0e7924
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1761
      have b0e8480 : y = (k y y) := by
        first
        | (have i₁ := b0e410 y
           have i₂ := b0e7924
           grind)
        | exact superpose b0e7924 b0e410
        | exact resolve b0e410 b0e7924
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e410 b0e7924
      have b0e14992 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e3389 y
           have i₂ := b0e8480
           grind)
        | exact superpose b0e8480 b0e3389
        | (have j0 := b0e3389 y
           grind)
        | exact resolve b0e3389 b0e8480
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3389 b0e8480
      have b0e14998 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e14992
      have b0e15008 : False := by grind
      exact b0e15008
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
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
        have b1e30 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ x) (σ y) X0 X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 x X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 X0 X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e30
          | exact resolve b1e30 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e41 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e36 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e36
          | exact resolve b1e36 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e125 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e40 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e40
          | exact resolve b1e40 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e154 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e125
        have b1e163 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e154
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e154
          | exact resolve b1e154 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e154
        have b1e190 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e163
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e163
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e163 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e163
        have b1e194 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e190
        have b1e198 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e194
             have i₂ := b1e41 y
             grind)
          | exact superpose b1e41 b1e194
          | exact resolve b1e194 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e194
        have b1e199 : y = (M.op y y) := by
          first
          | (have r₁ := b1e198
             have r₂ := b1e24
             grind)
          | exact resolve b1e198 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198
        have b1e200 : y = (M.op x y) := by
          first
          | (have i₁ := b1e199
             have i₂ := b1e41 y
             grind)
          | exact superpose b1e41 b1e199
          | exact resolve b1e199 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e199
        have b1e386 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e200
             grind)
          | exact superpose b1e200 b1e24
          | exact resolve b1e24 b1e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e200
        have b1e395 : False := by grind
        exact b1e395
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
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
        have b2e29 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b2e12 X0 x X4 X5
             have i₂ := b2e12 X0 x X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e82 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e132 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e1428 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e132
        have b2e1441 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1428 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1428
          | exact resolve b2e1428 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1428
        have b2e1473 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e82 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e1474 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1473
             have r₂ := b2e22
             grind)
          | exact resolve b2e1473 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1473
        have b2e1475 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1474
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1474
          | exact resolve b2e1474 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1474
        have b2e1476 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1475
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1475
          | exact resolve b2e1475 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1475
        have b2e1478 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1476
             grind)
          | exact superpose b2e1476 b2e22
          | exact resolve b2e22 b2e1476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1487 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 (σ x) X0 X1 (σ y) X2
             have i₂ := b2e1476
             grind)
          | exact superpose b2e1476 b2e29
          | exact resolve b2e29 b2e1476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e3630 : ∀ X0 X3 : G, (M.op (σ x) X0) = (M.op (σ x) X3) := by
          intro X0 X3
          first
          | (have i₁ := b2e1487 x x X3
             have i₂ := b2e1487 x x X0
             grind)
          | exact superpose b2e1487 b2e1487
          | exact resolve b2e1487 b2e1487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1487
        have b2e4150 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e1476
             have i₂ := b2e3630 (σ y) X0
             grind)
          | (have i₁ := b2e1476
             have i₂ := b2e3630 X0 (σ y)
             grind)
          | exact superpose b2e3630 b2e1476
          | exact resolve b2e1476 b2e3630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1476 b2e3630
        have b2e4543 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e1441 x
             have i₂ := b2e4150 (σ x)
             grind)
          | exact superpose b2e4150 b2e1441
          | exact resolve b2e1441 b2e4150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1441 b2e4150
        have b2e4600 : x = (k x x) := by
          first
          | (have i₁ := b2e4543
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e4543
          | exact resolve b2e4543 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4543
        have b2e4830 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e4600
             grind)
          | exact superpose b2e4600 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e4600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4600
        have b2e4831 : x = (M.op x x) := by grind
        clear b2e4830
        have b2e5232 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e4831
             grind)
          | exact superpose b2e4831 b2e20
          | exact resolve b2e20 b2e4831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4831
        have b2e5720 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1478
             have i₂ := b2e5232
             grind)
          | exact superpose b2e5232 b2e1478
          | exact resolve b2e1478 b2e5232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1478 b2e5232
        have b2e5722 : False := by grind
        exact b2e5722
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
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
        have b3e43 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ x) (σ x) X0 X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b3e12 X0 x X4 X5
             have i₂ := b3e12 X0 x X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 x X0 y X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e49 y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e49
          | exact resolve b3e49 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e53 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e53
          | exact resolve b3e53 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e78 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e49 X0 x
             have i₂ := b3e66 x
             grind)
          | exact superpose b3e66 b3e49
          | exact resolve b3e49 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e66
        have b3e93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e172 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e44 (σ x) X0 X1 (σ x) X2
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e44
          | exact resolve b3e44 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e197 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X3) X5) X6) := by
          intro X0 X1 X2 X3 X5 X6
          first
          | (have i₁ := b3e12 (M.op X0 X3) x X5 X6
             have i₂ := b3e44 X0 X3 (M.op (M.op X0 X3) x) X1 X2
             grind)
          | (have i₁ := b3e12 (M.op X0 X3) x X5 X6
             have i₂ := b3e44 X0 X1 X2 X3 (M.op (M.op X0 X3) x)
             grind)
          | exact superpose b3e44 b3e12
          | exact resolve b3e12 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e215 : ∀ X1 X2 : G, y = (M.op (M.op x X1) X2) := by
          intro X1 X2
          first
          | (have i₁ := b3e12 x x X1 X2
             have i₂ := b3e78 x
             grind)
          | exact superpose b3e78 b3e12
          | exact resolve b3e12 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e362 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e43 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1765 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e24
             have i₂ := b3e362 X0
             grind)
          | exact superpose b3e362 b3e24
          | exact resolve b3e24 b3e362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e362
        have b3e3288 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e93 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e93
          | exact resolve b3e93 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93
        have b3e3415 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e3288
        have b3e5545 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3415
             grind)
          | exact superpose b3e3415 b3e13
          | exact resolve b3e13 b3e3415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3415
        have b3e5562 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e5545
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e5545
          | exact resolve b3e5545 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5545
        have b3e5576 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e5562
             grind)
          | exact superpose b3e5562 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e5562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5562
        have b3e5577 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e5576
        have b3e5579 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e5577
             have r₂ := b3e20
             grind)
          | exact resolve b3e5577 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5577
        have b3e5910 : ∀ X0 : G, y = (M.op x X0) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e215 x X0
             have i₂ := b3e5579
             grind)
          | exact superpose b3e5579 b3e215
          | exact resolve b3e215 b3e5579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e215 b3e5579
        have b3e6570 : y ≠ y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e5910 x
             grind)
          | exact superpose b3e5910 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e5910 x
             grind)
          | exact resolve b3e20 b3e5910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5910
        have b3e6611 : (σ x) = (σ y) := by grind
        clear b3e6570
        have b3e6846 : ∀ X0 X1 X2 X5 : G, (M.op (M.op (M.op (σ x) X0) X1) X2) = (M.op (σ y) X5) := by
          intro X0 X1 X2 X5
          first
          | (have i₁ := b3e172 x x X5
             have i₂ := b3e197 (σ x) x x X0 X1 X2
             grind)
          | exact superpose b3e197 b3e172
          | exact resolve b3e172 b3e197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e172 b3e197
        have b3e6973 : ∀ X0 X1 X2 X5 : G, (M.op (M.op (M.op (σ x) X0) X1) X2) = (M.op (σ x) X5) := by
          intro X0 X1 X2 X5
          first
          | (have i₁ := b3e6846 X0 X1 X2 X5
             have i₂ := b3e6611
             grind)
          | exact superpose b3e6611 b3e6846
          | exact resolve b3e6846 b3e6611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6846
        have b3e7045 : ∀ X2 X5 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (σ x) X5) := by
          intro X2 X5
          first
          | (have i₁ := b3e6973 x x X2 X5
             have i₂ := b3e43 x x
             grind)
          | exact superpose b3e43 b3e6973
          | exact resolve b3e6973 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6973
        have b3e7083 : ∀ X5 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X5) := by
          intro X5
          first
          | (have i₁ := b3e7045 x X5
             have i₂ := b3e43 (σ y) x
             grind)
          | exact superpose b3e43 b3e7045
          | exact resolve b3e7045 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e7045
        have b3e7103 : ∀ X5 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X5) := by
          intro X5
          first
          | (have i₁ := b3e7083 X5
             have i₂ := b3e6611
             grind)
          | exact superpose b3e6611 b3e7083
          | exact resolve b3e7083 b3e6611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7083
        have b3e7110 : ∀ X5 : G, (σ y) = (M.op (σ x) X5) := by
          intro X5
          first
          | (have i₁ := b3e7103 X5
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e7103
          | exact resolve b3e7103 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7103
        have b3e7111 : ∀ X5 : G, (σ x) = (M.op (σ x) X5) := by
          intro X5
          first
          | (have i₁ := b3e7110 X5
             have i₂ := b3e6611
             grind)
          | exact superpose b3e6611 b3e7110
          | exact resolve b3e7110 b3e6611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7110
        have b3e7122 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e1765 X0
             have i₂ := b3e6611
             grind)
          | exact superpose b3e6611 b3e1765
          | exact resolve b3e1765 b3e6611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1765 b3e6611
        have b3e7150 : False := by grind
        exact b3e7150
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
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
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
          have b5e37 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b5e13 X0 x X4 X5
               have i₂ := b5e13 X0 x X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 y X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e39 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e39
            | exact resolve b5e39 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e45 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e45
            | exact resolve b5e45 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e61 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e64 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e61
          have b5e67 : x = (k x y) := by
            first
            | (have r₁ := b5e64
               have r₂ := b5e21
               grind)
            | exact resolve b5e64 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e80 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e83 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e39 X0 x
               have i₂ := b5e58 x
               grind)
            | exact superpose b5e58 b5e39
            | exact resolve b5e39 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e58
          have b5e99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e293 : ∀ X1 X2 : G, y = (M.op (M.op x X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b5e13 x x X1 X2
               have i₂ := b5e83 x
               grind)
            | exact superpose b5e83 b5e13
            | exact resolve b5e13 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e1428 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e80 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e1429 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1428
               have r₂ := b5e24
               grind)
            | exact resolve b5e1428 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1428
          have b5e1430 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1429
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1429
            | exact resolve b5e1429 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1429
          have b5e1431 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1430
               have i₂ := b5e67
               grind)
            | exact superpose b5e67 b5e1430
            | exact resolve b5e1430 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e1430
          have b5e1441 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 (σ x) X0 X1 (σ y) X2
               have i₂ := b5e1431
               grind)
            | exact superpose b5e1431 b5e37
            | exact resolve b5e37 b5e1431
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e1986 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e99
          have b5e2002 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1986 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1986
            | exact resolve b5e1986 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1986
          have b5e4097 : ∀ X0 X3 : G, (M.op (σ x) X0) = (M.op (σ x) X3) := by
            intro X0 X3
            first
            | (have i₁ := b5e1441 x x X3
               have i₂ := b5e1441 x x X0
               grind)
            | exact superpose b5e1441 b5e1441
            | exact resolve b5e1441 b5e1441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1441
          have b5e4613 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e1431
               have i₂ := b5e4097 (σ y) X0
               grind)
            | (have i₁ := b5e1431
               have i₂ := b5e4097 X0 (σ y)
               grind)
            | exact superpose b5e4097 b5e1431
            | exact resolve b5e1431 b5e4097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1431 b5e4097
          have b5e4906 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b5e2002 x
               have i₂ := b5e4613 (σ x)
               grind)
            | exact superpose b5e4613 b5e2002
            | exact resolve b5e2002 b5e4613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2002 b5e4613
          have b5e4966 : x = (k x x) := by
            first
            | (have i₁ := b5e4906
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e4906
            | exact resolve b5e4906 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4906
          have b5e5397 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e4966
               grind)
            | exact superpose b5e4966 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e4966
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4966
          have b5e5398 : x = (M.op x x) := by grind
          clear b5e5397
          have b5e5845 : ∀ X0 : G, y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e293 x X0
               have i₂ := b5e5398
               grind)
            | exact superpose b5e5398 b5e293
            | exact resolve b5e293 b5e5398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e293 b5e5398
          have b5e6021 : y ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e5845 x
               grind)
            | exact superpose b5e5845 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e5845 x
               grind)
            | exact resolve b5e21 b5e5845
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5845
          have b5e6068 : False := by grind
          exact b5e6068
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
        have b6e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e35 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b6e28
        have b6e39 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e35 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e35
          | exact resolve b6e35 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e81 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e88 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 ∨ (M.op (σ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e17 (σ x) X0
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e17 b6e22
          | (have j1 := b6e17 (σ x) X0
             grind)
          | exact resolve b6e22 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e90 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e81
             have r₂ := b6e20
             grind)
          | exact resolve b6e81 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e93 : x = (M.op x y) := by
          first
          | (have r₁ := b6e90
             have r₂ := b6e21
             grind)
          | exact resolve b6e90 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e95 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e21
          | exact resolve b6e21 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e97 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 x X0 y X1
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e12
          | exact resolve b6e12 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e235 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b6e97 x X2
             have i₂ := b6e97 x X0
             grind)
          | (have i₁ := b6e97 X0 x
             have i₂ := b6e97 X0 (M.op x X0)
             grind)
          | exact superpose b6e97 b6e97
          | exact resolve b6e97 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e356 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e93
             have i₂ := b6e235 y X0
             grind)
          | (have i₁ := b6e93
             have i₂ := b6e235 X0 y
             grind)
          | exact superpose b6e235 b6e93
          | exact resolve b6e93 b6e235
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93 b6e235
        have b6e1675 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by
          first
          | (have i₁ := b6e88 (σ (M.op (τ (σ x)) (τ (σ x))))
             have i₂ := b6e39 (σ x)
             grind)
          | exact superpose b6e39 b6e88
          | (have j0 := b6e88 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b6e88 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39 b6e88
        have b6e1678 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by
          first
          | (have i₁ := b6e1675
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1675
          | exact resolve b6e1675 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1675
        have b6e1684 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by
          first
          | (have i₁ := b6e1678
             have i₂ := b6e356 x
             grind)
          | exact superpose b6e356 b6e1678
          | exact resolve b6e1678 b6e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1678
        have b6e1687 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by
          first
          | (have i₁ := b6e1684
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1684
          | exact resolve b6e1684 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1684
        have b6e1689 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by
          first
          | (have i₁ := b6e1687
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1687
          | exact resolve b6e1687 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1687
        have b6e1691 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by
          first
          | (have i₁ := b6e1689
             have i₂ := b6e356 x
             grind)
          | exact superpose b6e356 b6e1689
          | exact resolve b6e1689 b6e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1689
        have b6e1692 : (σ x) = (σ y) ∨ (σ (M.op (τ (σ x)) (τ (σ x)))) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) := by grind
        clear b6e1691
        have b6e1695 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1692
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1692
          | exact resolve b6e1692 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1692
        have b6e1697 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1695
             have i₂ := b6e356 x
             grind)
          | exact superpose b6e356 b6e1695
          | exact resolve b6e1695 b6e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e356 b6e1695
        have b6e1699 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1697
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1697
          | exact resolve b6e1697 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1697
        have b6e1700 : (σ x) = (σ y) := by grind
        clear b6e1699
        have b6e1942 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1700
             grind)
          | exact superpose b6e1700 b6e13
          | exact resolve b6e13 b6e1700
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1700
        have b6e1943 : x = y := by
          first
          | (have i₁ := b6e1942
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1942
          | exact resolve b6e1942 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1942
        have b6e1948 : False := by grind
        exact b6e1948
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e29 X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e56 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e60 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e56
          have b7e62 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e23
               grind)
            | exact resolve b7e60 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e63 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e62
            | exact resolve b7e62 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e66 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e14
            | exact resolve b7e14 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : x = (k x y) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e66
            | exact resolve b7e66 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e93 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e94 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e93
               have r₂ := b7e21
               grind)
            | exact resolve b7e93 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e96 : x = (M.op x y) := by
            first
            | (have r₁ := b7e94
               have r₂ := b7e22
               grind)
            | exact resolve b7e94 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e108 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 x X0 y X1
               have i₂ := b7e96
               grind)
            | exact superpose b7e96 b7e13
            | exact resolve b7e13 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1484 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
            intro X0 X2
            first
            | (have i₁ := b7e108 x X2
               have i₂ := b7e108 x X0
               grind)
            | (have i₁ := b7e108 X0 x
               have i₂ := b7e108 X0 (M.op x X0)
               grind)
            | exact superpose b7e108 b7e108
            | exact resolve b7e108 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e1843 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e96
               have i₂ := b7e1484 y X0
               grind)
            | (have i₁ := b7e96
               have i₂ := b7e1484 X0 y
               grind)
            | exact superpose b7e1484 b7e96
            | exact resolve b7e96 b7e1484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96 b7e1484
          have b7e2006 : x = (k x x) := by grind
          clear b7e1843
          have b7e2594 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e74 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e2596 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e2594 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2594
          have b7e10681 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e2596 x
               have i₂ := b7e2006
               grind)
            | exact superpose b7e2006 b7e2596
            | (have j0 := b7e2596 x
               grind)
            | exact resolve b7e2596 b7e2006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2006 b7e2596
          have b7e10689 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e10681
          have b7e10716 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e40 (σ x) X0
               have i₂ := b7e10689
               grind)
            | exact superpose b7e10689 b7e40
            | exact resolve b7e40 b7e10689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e10689
          have b7e10870 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e10716 (σ x)
               grind)
            | exact superpose b7e10716 b7e23
            | (have r₁ := b7e23
               have r₂ := b7e10716 (σ x)
               grind)
            | exact resolve b7e23 b7e10716
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10716
          have b7e10954 : False := by grind
          exact b7e10954
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
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e1095 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e1096 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1095
               have r₂ := b8e24
               grind)
            | exact resolve b8e1095 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1095
          have b8e1097 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1096
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1096
            | exact resolve b8e1096 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1096
          have b8e1098 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1097
               grind)
            | exact superpose b8e1097 b8e20
            | exact resolve b8e20 b8e1097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1097
          have b8e1603 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1098
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1098
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1098 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1098
          have b8e1604 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1603
          have b8e1606 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1604
               have r₂ := b8e21
               grind)
            | exact resolve b8e1604 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1604
          have b8e1608 : False := by grind
          exact b8e1608

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4411 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4411 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
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
      have b0e63 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e66 : False := by grind
      exact b0e66
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X0 X3
               have i₂ := b4e13 X2 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X2 (M.op X2 X0)
               have i₂ := b4e13 X2 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) X0) := by
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
          have b4e39 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y X0) := by
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
          have b4e44 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y X1
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X0) = (M.op X0 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X0 y) X1
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e47 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e46 X0 X1
               have i₂ := b4e36 X0 y X1 X0
               grind)
            | exact superpose b4e36 b4e46
            | exact resolve b4e46 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e68 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X1 (M.op y X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op y X2) X0
               have i₂ := b4e44 X0 X2
               grind)
            | exact superpose b4e44 b4e13
            | exact resolve b4e13 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e68 X0 X1 x
               have i₂ := b4e47 X1 (M.op y x)
               grind)
            | exact superpose b4e47 b4e68
            | exact resolve b4e68 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e68
          have b4e78 : ∀ X1 : G, (M.op y X1) = (M.op X1 (M.op y X1)) := by
            intro X1
            first
            | (have i₁ := b4e76 x X1
               have i₂ := b4e44 X1 x
               grind)
            | exact superpose b4e44 b4e76
            | exact resolve b4e76 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e87 : y = (M.op x y) := by
            first
            | (have i₁ := b4e78 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e78
            | exact resolve b4e78 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e170 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e35 X0 X1 X2 (M.op y X0)
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e35
            | exact resolve b4e35 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e226 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e170 X0 X1 X2
               have i₂ := b4e44 X2 X0
               grind)
            | exact superpose b4e44 b4e170
            | exact resolve b4e170 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e170
          have b4e472 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (σ y)) X2) = (M.op (σ y) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 X2
               have i₂ := b4e36 X0 X1 (σ y) X2
               grind)
            | exact superpose b4e36 b4e38
            | exact resolve b4e38 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e38
          have b4e512 : ∀ X2 : G, (M.op y X2) = (M.op (σ y) X2) := by
            intro X2
            first
            | (have i₁ := b4e472 x x X2
               have i₂ := b4e226 (M.op x x) (σ y) X2
               grind)
            | exact superpose b4e226 b4e472
            | exact resolve b4e472 b4e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226 b4e472
          have b4e606 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e512 (σ x)
               grind)
            | exact superpose b4e512 b4e24
            | exact resolve b4e24 b4e512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e512
          have b4e948 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e78 (σ x)
               have i₂ := b4e606
               grind)
            | exact superpose b4e606 b4e78
            | exact resolve b4e78 b4e606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78 b4e606
          have b4e2143 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e948
               grind)
            | exact superpose b4e948 b4e20
            | exact resolve b4e20 b4e948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e948
          have b4e2171 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e2143
               have i₂ := b4e87
               grind)
            | exact superpose b4e87 b4e2143
            | exact resolve b4e2143 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87 b4e2143
          have b4e2172 : False := by grind
          exact b4e2172
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 X2) X0 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
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
          have b5e35 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y X0) := by
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
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 X2 (M.op X2 X0)
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X0) = (M.op X0 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X0 y) X1
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e43 X0 X1
               have i₂ := b5e36 X0 y X1 X0
               grind)
            | exact superpose b5e36 b5e43
            | exact resolve b5e43 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e45 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e48 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X0 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 (M.op X1 X2) X0
               grind)
            | (have r₁ := b5e17 X0 (M.op X0 (M.op X0 X0))
               have r₂ := b5e13 X0 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : x = y ∨ x = (k x y) := by grind
          clear b5e45
          have b5e50 : x = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e61 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X1 (M.op y X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (M.op y X2) X0
               have i₂ := b5e41 X0 X2
               grind)
            | exact superpose b5e41 b5e13
            | exact resolve b5e13 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op y X0) X1)) = (M.op (M.op X1 X2) (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op y X0) X1 X2
               have i₂ := b5e41 (M.op (M.op y X0) X1) X0
               grind)
            | exact superpose b5e41 b5e13
            | exact resolve b5e13 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e67 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op y X0)) = (M.op y (M.op y X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e63 X0 X1 X2
               have i₂ := b5e41 X1 X0
               grind)
            | exact superpose b5e41 b5e63
            | exact resolve b5e63 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e69 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e61 X0 X1 x
               have i₂ := b5e44 X1 (M.op y x)
               grind)
            | exact superpose b5e44 b5e61
            | exact resolve b5e61 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e71 : ∀ X1 : G, (M.op y X1) = (M.op X1 (M.op y X1)) := by
            intro X1
            first
            | (have i₁ := b5e69 x X1
               have i₂ := b5e41 X1 x
               grind)
            | exact superpose b5e41 b5e69
            | exact resolve b5e69 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e73 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b5e77 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e78 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e73 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e73
            | exact resolve b5e73 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e79 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e78
          have b5e80 : y = (M.op x y) := by
            first
            | (have i₁ := b5e71 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e71
            | exact resolve b5e71 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e108 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e80
               grind)
            | exact superpose b5e80 b5e13
            | exact resolve b5e13 b5e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e113 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e115 : ∀ X0 X1 : G, (M.op X1 (M.op y X1)) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e113 X0 X1
               have i₂ := b5e44 X1 (σ X0)
               grind)
            | exact superpose b5e44 b5e113
            | exact resolve b5e113 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113
          have b5e116 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e115 X0 X1
               have i₂ := b5e71 X1
               grind)
            | (have i₁ := b5e115 X0 y
               have i₂ := b5e71 (M.op y y)
               grind)
            | exact superpose b5e71 b5e115
            | exact resolve b5e115 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e115
          have b5e117 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e108 (M.op X0 X1)
               have i₂ := b5e13 x X0 X1
               grind)
            | exact superpose b5e13 b5e108
            | exact resolve b5e108 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e133 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x (M.op y x))) := by
            intro X0 X1
            first
            | (have i₁ := b5e117 X0 X1
               have i₂ := b5e44 x X0
               grind)
            | exact superpose b5e44 b5e117
            | exact resolve b5e117 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e117
          have b5e136 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op y x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e133 X0 X1
               have i₂ := b5e71 x
               grind)
            | exact superpose b5e71 b5e133
            | exact resolve b5e133 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133
          have b5e139 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e136 X0 X1
               have i₂ := b5e67 x X0 X1
               grind)
            | exact superpose b5e67 b5e136
            | exact resolve b5e136 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e136
          have b5e156 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 (M.op (M.op X0 X1) y) X2
               have i₂ := b5e35 (M.op X0 X1)
               grind)
            | exact superpose b5e35 b5e34
            | exact resolve b5e34 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e162 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 X2 (M.op y X0)
               have i₂ := b5e71 X0
               grind)
            | exact superpose b5e71 b5e34
            | exact resolve b5e34 b5e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e217 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e162 X0 X1 X2
               have i₂ := b5e41 X2 X0
               grind)
            | exact superpose b5e41 b5e162
            | exact resolve b5e162 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e162
          have b5e222 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op y (M.op y X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e156 X0 X1 X2
               have i₂ := b5e13 y X0 X1
               grind)
            | exact superpose b5e13 b5e156
            | exact resolve b5e156 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e156
          have b5e240 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op y (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e222 X0 X1 x
               have i₂ := b5e217 X0 x (M.op y (M.op y X0))
               grind)
            | exact superpose b5e217 b5e222
            | exact resolve b5e222 b5e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e222
          have b5e247 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e240 X0 X1
               have i₂ := b5e139 y (M.op y X0)
               grind)
            | (have i₁ := b5e240 X0 X1
               have i₂ := b5e139 (M.op y X0) X1
               grind)
            | exact superpose b5e139 b5e240
            | exact resolve b5e240 b5e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e240
          have b5e254 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b5e247 X0 X1
               have i₂ := b5e35 y
               grind)
            | exact superpose b5e35 b5e247
            | exact resolve b5e247 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e247
          have b5e341 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 (M.op X2 X3) X1 X0 X4
               have i₂ := b5e36 X2 X3 X1 X0
               grind)
            | exact superpose b5e36 b5e34
            | exact resolve b5e34 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e36
          have b5e359 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e341 X0 X1 x x x
               have i₂ := b5e217 (M.op x x) x X0
               grind)
            | exact superpose b5e217 b5e341
            | exact resolve b5e341 b5e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e341
          have b5e2207 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op (τ X0) (τ X0))
               have i₂ := b5e79 X0
               grind)
            | exact superpose b5e79 b5e30
            | exact resolve b5e30 b5e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e79
          have b5e2213 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e2207 X0
               have i₂ := b5e217 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e217 b5e2207
            | exact resolve b5e2207 b5e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2207
          have b5e2215 : ∀ X0 : G, (M.op y y) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e2213 X0
               have i₂ := b5e254 X0 X0
               grind)
            | exact superpose b5e254 b5e2213
            | exact resolve b5e2213 b5e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2213
          have b5e2216 : ∀ X0 : G, (M.op y y) = (σ (M.op y (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e2215 X0
               have i₂ := b5e217 (τ X0) (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b5e217 b5e2215
            | exact resolve b5e2215 b5e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2215
          have b5e2217 : ∀ X0 : G, (M.op y y) = (σ (M.op y (M.op y (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e2216 X0
               have i₂ := b5e139 (τ X0) (τ X0)
               grind)
            | exact superpose b5e139 b5e2216
            | exact resolve b5e2216 b5e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2216
          have b5e2218 : (M.op y y) = (σ (M.op y (M.op y y))) := by
            first
            | (have i₁ := b5e2217 x
               have i₂ := b5e139 y (τ x)
               grind)
            | (have i₁ := b5e2217 x
               have i₂ := b5e139 (τ x) x
               grind)
            | exact superpose b5e139 b5e2217
            | exact resolve b5e2217 b5e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2217
          have b5e2219 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e2218
               have i₂ := b5e254 y y
               grind)
            | exact superpose b5e254 b5e2218
            | exact resolve b5e2218 b5e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2218
          have b5e2280 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have j0 := b5e48 X0 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e2281 : ∀ X0 : G, (M.op y X0) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e2280 X0
               have i₂ := b5e359 X0 X0
               grind)
            | exact superpose b5e359 b5e2280
            | (have j0 := b5e2280 X0
               grind)
            | exact resolve b5e2280 b5e359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2280
          have b5e2332 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e2281 X0
               have i₂ := b5e359 X0 X0
               grind)
            | exact superpose b5e359 b5e2281
            | (have j0 := b5e2281 X0
               grind)
            | exact resolve b5e2281 b5e359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2281
          have b5e2435 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e77 X0 (M.op y y)
               have i₂ := b5e2219
               grind)
            | exact superpose b5e2219 b5e77
            | exact resolve b5e77 b5e2219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e2439 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e2219
               grind)
            | exact superpose b5e2219 b5e14
            | exact resolve b5e14 b5e2219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2470 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ X0) (M.op (σ X0) X2))) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e33 (σ X0) X2 X3 (σ X1)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e33
            | (have j1 := b5e53 X0 X1
               grind)
            | exact resolve b5e33 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e2483 : ∀ X0 X1 : G, (M.op y y) = (M.op y (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e254 (σ X0) (σ X1)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e254
            | (have j1 := b5e53 X0 X1
               grind)
            | exact resolve b5e254 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e2539 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) (M.op X2 X3)) = (M.op y (M.op (σ X0) (M.op (σ X0) X2))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e2470 X0 X1 X2 X3
               have i₂ := b5e217 X2 X3 (M.op (σ X0) (M.op (σ X0) X2))
               grind)
            | exact superpose b5e217 b5e2470
            | (have j0 := b5e2470 X0 X1 X2 X3
               grind)
            | exact resolve b5e2470 b5e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e217 b5e2470
          have b5e2569 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op y (σ X0))) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e2539 X0 X1 X2 X3
               have i₂ := b5e139 (σ X0) (M.op (σ X0) X2)
               grind)
            | exact superpose b5e139 b5e2539
            | (have j0 := b5e2539 X0 X1 X2 X3
               grind)
            | exact resolve b5e2539 b5e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2539
          have b5e2581 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op y y)) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e2569 X0 X1 X2 X3
               have i₂ := b5e139 y (σ X0)
               grind)
            | (have i₁ := b5e2569 X0 X1 X2 X3
               have i₂ := b5e139 (σ X0) X1
               grind)
            | exact superpose b5e139 b5e2569
            | (have j0 := b5e2569 X0 X1 X2 X3
               grind)
            | exact resolve b5e2569 b5e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139 b5e2569
          have b5e2590 : ∀ X0 X1 X2 X3 : G, (M.op y y) = (M.op (σ (k X0 X1)) (M.op X2 X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e2581 X0 X1 X2 X3
               have i₂ := b5e254 y y
               grind)
            | exact superpose b5e254 b5e2581
            | (have j0 := b5e2581 X0 X1 X2 X3
               grind)
            | exact resolve b5e2581 b5e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e254 b5e2581
          have b5e4018 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op y (σ X0)))) ∨ (σ X0) = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e101 X0 (M.op y (σ X0))
               have i₂ := b5e2332 (σ X0)
               grind)
            | exact superpose b5e2332 b5e101
            | (have j1 := b5e2332 (σ X0)
               grind)
            | exact resolve b5e101 b5e2332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101 b5e2332
          have b5e4023 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 ∨ (σ X0) = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e4018 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4018
            | (have j0 := b5e4018 X0
               grind)
            | exact resolve b5e4018 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4018
          have b5e19079 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ x) (M.op X0 X1)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b5e2590 x y X0 X1
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e2590
            | (have j0 := b5e2590 x y x x
               grind)
            | exact resolve b5e2590 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e2590
          have b5e19285 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ x) (M.op X0 X1)) ∨ (σ x) = (σ y) := by
            intro X0 X1
            first
            | (have j0 := b5e19079 X0 X1
               grind)
            | (have r₁ := b5e19079 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e19079 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19079
          have b5e19310 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ x) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e19285 X0 X1
               grind)
            | (have r₁ := b5e19285 X0 X1
               have r₂ := b5e23
               grind)
            | exact resolve b5e19285 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19285
          have b5e19451 : (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e71 (σ x)
               have i₂ := b5e19310 y (σ x)
               grind)
            | exact superpose b5e19310 b5e71
            | exact resolve b5e71 b5e19310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71 b5e19310
          have b5e26512 : x = (k x (τ (M.op y y))) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e4023 x
               have i₂ := b5e19451
               grind)
            | exact superpose b5e19451 b5e4023
            | exact resolve b5e4023 b5e19451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4023
          have b5e26566 : x = (k x (M.op y y)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e26512
               have i₂ := b5e2439
               grind)
            | exact superpose b5e2439 b5e26512
            | exact resolve b5e26512 b5e2439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26512
          have b5e26634 : (τ x) = (k (τ x) (M.op y y)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e2435 x
               have i₂ := b5e26566
               grind)
            | exact superpose b5e26566 b5e2435
            | exact resolve b5e2435 b5e26566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2435 b5e26566
          have b5e42026 : (M.op y y) = (M.op y (σ (τ x))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (τ x))) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e2483 (τ x) (M.op y y)
               have i₂ := b5e26634
               grind)
            | exact superpose b5e26634 b5e2483
            | (have j0 := b5e2483 (τ x) (M.op y y)
               grind)
            | exact resolve b5e2483 b5e26634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2483 b5e26634
          have b5e42172 : (M.op y x) = (M.op y y) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (τ x))) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42026
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e42026
            | exact resolve b5e42026 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42026
          have b5e42208 : y = (M.op y y) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (τ x))) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42172
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e42172
            | exact resolve b5e42172 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42172
          have b5e42234 : (σ (M.op y y)) = (M.op y (σ (τ x))) ∨ y = (M.op y y) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42208
               have i₂ := b5e116 y (σ (τ x))
               grind)
            | exact superpose b5e116 b5e42208
            | exact resolve b5e42208 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116 b5e42208
          have b5e42257 : (M.op y x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42234
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e42234
            | exact resolve b5e42234 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42234
          have b5e42264 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42257
               have i₂ := b5e2219
               grind)
            | exact superpose b5e2219 b5e42257
            | exact resolve b5e42257 b5e2219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42257
          have b5e42267 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42264
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e42264
            | exact resolve b5e42264 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42264
          have b5e42268 : y = (M.op y y) ∨ (σ (M.op y y)) = (σ (τ x)) ∨ (σ x) = (M.op y y) := by grind
          clear b5e42267
          have b5e42269 : x = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b5e42268
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e42268
            | exact resolve b5e42268 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42268
          have b5e42270 : (σ x) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e42269
               have i₂ := b5e2219
               grind)
            | exact superpose b5e2219 b5e42269
            | exact resolve b5e42269 b5e2219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42269
          have b5e46111 : (σ x) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e2439
               have i₂ := b5e42270
               grind)
            | exact superpose b5e42270 b5e2439
            | exact resolve b5e2439 b5e42270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2439
          have b5e46232 : x ≠ (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b5e42270
          have b5e46300 : x = (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b5e46111
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e46111
            | exact resolve b5e46111 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46111
          have b5e46317 : x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b5e46300
               have r₂ := b5e46232
               grind)
            | exact resolve b5e46300 b5e46232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46232 b5e46300
          have b5e46544 : x = (M.op y x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e359 y y
               have i₂ := b5e46317
               grind)
            | exact superpose b5e46317 b5e359
            | exact resolve b5e359 b5e46317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e359 b5e46317
          have b5e46559 : x = y ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e46544
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e46544
            | exact resolve b5e46544 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46544
          have b5e46600 : y = (M.op y y) := by
            first
            | (have r₁ := b5e46559
               have r₂ := b5e21
               grind)
            | exact resolve b5e46559 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46559
          have b5e47564 : y = (σ y) := by
            first
            | (have i₁ := b5e2219
               have i₂ := b5e46600
               grind)
            | exact superpose b5e46600 b5e2219
            | exact resolve b5e2219 b5e46600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2219
          have b5e48073 : y ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e47564
               grind)
            | exact superpose b5e47564 b5e24
            | exact resolve b5e24 b5e47564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47564
          have b5e48170 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b5e48073
               have i₂ := b5e19451
               grind)
            | exact superpose b5e19451 b5e48073
            | exact resolve b5e48073 b5e19451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19451 b5e48073
          have b5e48175 : False := by grind
          exact b5e48175
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X2 X0) X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
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
          have b7e36 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ y) X0) := by
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
          have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e33 X0 X1 X2 X3
               have i₂ := b7e37 X2 X0 X3 X2
               grind)
            | exact superpose b7e37 b7e33
            | exact resolve b7e33 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e40 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ y)) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e32 X0
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e32
            | exact resolve b7e32 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e48
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e51
               have r₂ := b7e23
               grind)
            | exact resolve b7e51 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e53 : (σ x) = (σ (k x y)) := by
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
          have b7e56 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e14
            | exact resolve b7e14 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e57 : x = (k x y) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e56
            | exact resolve b7e56 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e63 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e53
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e53 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e64 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e22
               grind)
            | exact resolve b7e63 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e65 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e21
               grind)
            | exact resolve b7e64 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e67 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e68 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e70 : x = (M.op x y) := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e21
               grind)
            | exact resolve b7e68 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e85 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e13
            | exact resolve b7e13 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e112 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 (σ y) X0 X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e113 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 (σ X0) X1 X2 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e35
            | exact resolve b7e35 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e114 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 x X0 X1 y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e35
            | exact resolve b7e35 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e129 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op y y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e112 x X1
               have i₂ := b7e113 y x X1
               grind)
            | exact superpose b7e113 b7e112
            | exact resolve b7e112 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e143 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b7e36 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e36
            | exact resolve b7e36 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e149 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 X0 (M.op X0 (σ y)) X1 X2
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e35
            | exact resolve b7e35 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e151 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 (σ y))
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e152 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X0 (σ y)) X1
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e155 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e152 X0 X1
               have i₂ := b7e37 X0 (σ y) X1 X0
               grind)
            | exact superpose b7e37 b7e152
            | exact resolve b7e152 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37 b7e152
          have b7e156 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) X1) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e151 X0 X1
               have i₂ := b7e113 y X0 X1
               grind)
            | exact superpose b7e113 b7e151
            | exact resolve b7e151 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e157 : ∀ X0 X1 X2 : G, (M.op (σ (M.op y y)) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e149 X0 X1 X2
               have i₂ := b7e113 y X0 X1
               grind)
            | exact superpose b7e113 b7e149
            | exact resolve b7e149 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113 b7e149
          have b7e161 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e156 X0 X1
               have i₂ := b7e129 X1
               grind)
            | exact superpose b7e129 b7e156
            | exact resolve b7e156 b7e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e162 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e157 X0 X1 X2
               have i₂ := b7e129 X1
               grind)
            | exact superpose b7e129 b7e157
            | exact resolve b7e157 b7e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e157
          have b7e166 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e85 (M.op X0 X1)
               have i₂ := b7e13 x X0 X1
               grind)
            | exact superpose b7e13 b7e85
            | exact resolve b7e85 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e186 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (σ y) (M.op x (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e166 X0 X1
               have i₂ := b7e162 X0 (M.op x (M.op x X0)) X1
               grind)
            | exact superpose b7e162 b7e166
            | exact resolve b7e166 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e166
          have b7e193 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (σ y) (M.op (σ y) x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e186 X0 X1
               have i₂ := b7e161 X0 x
               grind)
            | exact superpose b7e161 b7e186
            | exact resolve b7e186 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e186
          have b7e200 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e193 X0 X1
               have i₂ := b7e85 (σ y)
               grind)
            | exact superpose b7e85 b7e193
            | exact resolve b7e193 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e193
          have b7e209 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b7e40 (σ x)
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e40
            | exact resolve b7e40 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e212 : (σ (M.op y y)) = (M.op (M.op x (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e40 (M.op (σ x) x)
               have i₂ := b7e85 (σ x)
               grind)
            | exact superpose b7e85 b7e40
            | exact resolve b7e40 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e223 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) X0) = (M.op X0 (M.op X0 (M.op (σ x) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op (σ x) X1) (σ y)
               have i₂ := b7e40 X1
               grind)
            | exact superpose b7e40 b7e13
            | exact resolve b7e13 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e226 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e223 X0 x
               have i₂ := b7e155 X0 (M.op (σ x) x)
               grind)
            | exact superpose b7e155 b7e223
            | exact resolve b7e223 b7e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e155 b7e223
          have b7e232 : (σ (M.op y y)) = (M.op (σ y) (M.op (σ y) x)) := by
            first
            | (have i₁ := b7e212
               have i₂ := b7e13 (σ y) x (σ x)
               grind)
            | exact superpose b7e13 b7e212
            | exact resolve b7e212 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e212
          have b7e236 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e226 X0
               have i₂ := b7e129 X0
               grind)
            | exact superpose b7e129 b7e226
            | exact resolve b7e226 b7e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e129 b7e226
          have b7e238 : (σ (M.op y y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e232
               have i₂ := b7e85 (σ y)
               grind)
            | exact superpose b7e85 b7e232
            | exact resolve b7e232 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e232
          have b7e243 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) x) X0) := by
            intro X0
            first
            | (have i₁ := b7e114 (M.op x (σ y)) X0
               have i₂ := b7e36 x
               grind)
            | exact superpose b7e36 b7e114
            | exact resolve b7e114 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e260 : ∀ X0 : G, (M.op (σ y) (M.op x X0)) = (M.op x (M.op (M.op x X0) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e36 (M.op x X0)
               have i₂ := b7e114 X0 (M.op (M.op x X0) (σ y))
               grind)
            | exact superpose b7e114 b7e36
            | exact resolve b7e36 b7e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e114
          have b7e266 : ∀ X0 : G, (M.op x (σ y)) = (M.op (σ y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e260 X0
               have i₂ := b7e200 (M.op x X0) (σ y)
               grind)
            | exact superpose b7e200 b7e260
            | exact resolve b7e260 b7e200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e260
          have b7e274 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e243 X0
               have i₂ := b7e162 (σ y) X0 x
               grind)
            | exact superpose b7e162 b7e243
            | exact resolve b7e243 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e243
          have b7e277 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e266 X0
               have i₂ := b7e238
               grind)
            | exact superpose b7e238 b7e266
            | exact resolve b7e266 b7e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266
          have b7e285 : ∀ X0 : G, (σ (M.op y y)) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e277 X0
               have i₂ := b7e274 (M.op x X0)
               grind)
            | exact superpose b7e274 b7e277
            | exact resolve b7e277 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e277
          have b7e291 : (σ (M.op y y)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e285 x
               have i₂ := b7e161 x x
               grind)
            | exact superpose b7e161 b7e285
            | exact resolve b7e285 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e285
          have b7e295 : (σ (M.op y y)) = (M.op x x) := by
            first
            | (have i₁ := b7e291
               have i₂ := b7e274 x
               grind)
            | exact superpose b7e274 b7e291
            | exact resolve b7e291 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e291
          have b7e539 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e39 (σ X0) (σ X0) X1 X2
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e39
            | exact resolve b7e39 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e564 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op (M.op X3 X4) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e39 X0 X1 X2 (M.op X2 X3)
               have i₂ := b7e13 X2 X3 X4
               grind)
            | exact superpose b7e13 b7e39
            | exact resolve b7e39 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e650 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op (σ y) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e564 X0 X1 X2 x x
               have i₂ := b7e162 x X2 x
               grind)
            | exact superpose b7e162 b7e564
            | exact resolve b7e564 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e564
          have b7e670 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e539 X0 X1 x
               have i₂ := b7e161 x X1
               grind)
            | exact superpose b7e161 b7e539
            | exact resolve b7e539 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e539
          have b7e701 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op (σ y) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e650 X0 X1 X2
               have i₂ := b7e236 X2
               grind)
            | exact superpose b7e236 b7e650
            | exact resolve b7e650 b7e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e236 b7e650
          have b7e716 : ∀ X0 X1 : G, (M.op x X1) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e670 X0 X1
               have i₂ := b7e274 X1
               grind)
            | exact superpose b7e274 b7e670
            | exact resolve b7e670 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e670
          have b7e737 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op x X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e701 X0 X1 X2
               have i₂ := b7e274 X2
               grind)
            | exact superpose b7e274 b7e701
            | exact resolve b7e701 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e701
          have b7e764 : ∀ X2 : G, (M.op x X2) = (M.op X2 (M.op (σ y) X2)) := by
            intro X2
            first
            | (have i₁ := b7e737 x x X2
               have i₂ := b7e162 x X2 x
               grind)
            | exact superpose b7e162 b7e737
            | exact resolve b7e737 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e737
          have b7e787 : ∀ X2 : G, (M.op x X2) = (M.op X2 (M.op x X2)) := by
            intro X2
            first
            | (have i₁ := b7e764 X2
               have i₂ := b7e274 X2
               grind)
            | exact superpose b7e274 b7e764
            | exact resolve b7e764 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e764
          have b7e1175 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op x x) (M.op x x)) := by
            first
            | (have i₁ := b7e30 (M.op y y)
               have i₂ := b7e295
               grind)
            | exact superpose b7e295 b7e30
            | exact resolve b7e30 b7e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e1178 : (M.op y y) = (τ (M.op x x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e295
               grind)
            | exact superpose b7e295 b7e14
            | exact resolve b7e14 b7e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1179 : (M.op (σ y) (M.op x x)) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b7e1175
               have i₂ := b7e162 x (M.op x x) x
               grind)
            | exact superpose b7e162 b7e1175
            | exact resolve b7e1175 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1175
          have b7e1180 : (M.op (σ y) (M.op x x)) = (σ (M.op (σ y) (M.op y y))) := by
            first
            | (have i₁ := b7e1179
               have i₂ := b7e162 y (M.op y y) y
               grind)
            | exact superpose b7e162 b7e1179
            | exact resolve b7e1179 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e162 b7e1179
          have b7e1181 : (M.op (σ y) (M.op x x)) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b7e1180
               have i₂ := b7e274 (M.op y y)
               grind)
            | exact superpose b7e274 b7e1180
            | exact resolve b7e1180 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1180
          have b7e1182 : (M.op (σ y) (M.op x x)) = (σ (M.op x (σ y))) := by
            first
            | (have i₁ := b7e1181
               have i₂ := b7e200 y y
               grind)
            | exact superpose b7e200 b7e1181
            | exact resolve b7e1181 b7e200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e200 b7e1181
          have b7e1183 : (M.op (σ y) (M.op x x)) = (σ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e1182
               have i₂ := b7e238
               grind)
            | exact superpose b7e238 b7e1182
            | exact resolve b7e1182 b7e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1182
          have b7e1184 : (σ (M.op x x)) = (M.op (σ y) (M.op x x)) := by
            first
            | (have i₁ := b7e1183
               have i₂ := b7e295
               grind)
            | exact superpose b7e295 b7e1183
            | exact resolve b7e1183 b7e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1183
          have b7e1185 : (σ (M.op x x)) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b7e1184
               have i₂ := b7e274 (M.op x x)
               grind)
            | exact superpose b7e274 b7e1184
            | exact resolve b7e1184 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1184
          have b7e1186 : (M.op x x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e1185
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e1185
            | exact resolve b7e1185 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e1185
          have b7e2448 : (M.op x x) = (τ (M.op x x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e1186
               grind)
            | exact superpose b7e1186 b7e14
            | exact resolve b7e14 b7e1186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2449 : (M.op y y) = (M.op x x) := by
            first
            | (have i₁ := b7e2448
               have i₂ := b7e1178
               grind)
            | exact superpose b7e1178 b7e2448
            | exact resolve b7e2448 b7e1178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2448
          have b7e2673 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e1186
               have i₂ := b7e2449
               grind)
            | exact superpose b7e2449 b7e1186
            | exact resolve b7e1186 b7e2449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2674 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b7e1178
               have i₂ := b7e2449
               grind)
            | exact superpose b7e2449 b7e1178
            | exact resolve b7e1178 b7e2449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1178
          have b7e2712 : x = (M.op y x) := by
            first
            | (have i₁ := b7e787 y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e787
            | exact resolve b7e787 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e787
          have b7e3888 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (σ (M.op y y)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 x (σ y) X0 X1
               have i₂ := b7e238
               grind)
            | exact superpose b7e238 b7e39
            | exact resolve b7e39 b7e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e238
          have b7e3899 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e3888 X0 X1
               have i₂ := b7e716 y X0
               grind)
            | exact superpose b7e716 b7e3888
            | exact resolve b7e3888 b7e716
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e716 b7e3888
          have b7e4176 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op x X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e3899 X0 X1
               grind)
            | exact superpose b7e3899 b7e13
            | exact resolve b7e13 b7e3899
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3899
          have b7e5701 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e17 (σ y) (σ (M.op x x))
               have i₂ := b7e209
               grind)
            | exact superpose b7e209 b7e17
            | (have j0 := b7e17 (σ y) (σ (M.op x x))
               grind)
            | exact resolve b7e17 b7e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e209
          have b7e5735 : (σ (M.op y y)) ≠ (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e5701
               have i₂ := b7e1186
               grind)
            | exact superpose b7e1186 b7e5701
            | exact resolve b7e5701 b7e1186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5701
          have b7e5752 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
            first
            | (have r₁ := b7e5735
               have r₂ := b7e295
               grind)
            | exact resolve b7e5735 b7e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5735
          have b7e5764 : (σ y) = (M.op x x) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e5752
               have i₂ := b7e1186
               grind)
            | exact superpose b7e1186 b7e5752
            | exact resolve b7e5752 b7e1186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1186 b7e5752
          have b7e5773 : (σ y) = (M.op y y) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e5764
               have i₂ := b7e2449
               grind)
            | exact superpose b7e2449 b7e5764
            | exact resolve b7e5764 b7e2449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5764
          have b7e5778 : (σ y) = (σ (k y (M.op x x))) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e5773
               have i₂ := b7e19 y (M.op x x)
               grind)
            | exact superpose b7e19 b7e5773
            | exact resolve b7e5773 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5773
          have b7e5782 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e5778
               have i₂ := b7e2449
               grind)
            | exact superpose b7e2449 b7e5778
            | exact resolve b7e5778 b7e2449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2449 b7e5778
          have b7e39490 : (σ y) = (σ (M.op y (M.op y y))) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e5782
               have i₂ := b7e18 y (M.op y y)
               grind)
            | exact superpose b7e18 b7e5782
            | (have j1 := b7e18 y (M.op y y)
               grind)
            | exact resolve b7e5782 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5782
          have b7e39571 : (σ y) = (σ (M.op (σ y) y)) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39490
               have i₂ := b7e161 y y
               grind)
            | exact superpose b7e161 b7e39490
            | exact resolve b7e39490 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39490
          have b7e39577 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39571
               have i₂ := b7e274 y
               grind)
            | exact superpose b7e274 b7e39571
            | exact resolve b7e39571 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39571
          have b7e39583 : (σ x) = (σ y) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39577
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e39577
            | exact resolve b7e39577 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e39577
          have b7e39586 : (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b7e39583
               have r₂ := b7e23
               grind)
            | exact resolve b7e39583 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39583
          have b7e39587 : (M.op y y) = (M.op y (M.op y y)) ∨ (σ y) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39586
               have i₂ := b7e13 y y y
               grind)
            | exact superpose b7e13 b7e39586
            | exact resolve b7e39586 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39586
          have b7e39588 : (M.op y y) = (M.op (σ y) y) ∨ (σ y) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39587
               have i₂ := b7e161 y y
               grind)
            | exact superpose b7e161 b7e39587
            | exact resolve b7e39587 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e161 b7e39587
          have b7e39589 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39588
               have i₂ := b7e274 y
               grind)
            | exact superpose b7e274 b7e39588
            | exact resolve b7e39588 b7e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e274 b7e39588
          have b7e39590 : (σ y) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e39589
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e39589
            | exact resolve b7e39589 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e39589
          have b7e54461 : (σ y) = (τ (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e2674
               have i₂ := b7e39590
               grind)
            | exact superpose b7e39590 b7e2674
            | exact resolve b7e2674 b7e39590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2674
          have b7e54550 : y ≠ (σ y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b7e39590
          have b7e54599 : y = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e54461
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e54461
            | exact resolve b7e54461 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54461
          have b7e54618 : x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b7e54599
               have r₂ := b7e54550
               grind)
            | exact resolve b7e54599 b7e54550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54550 b7e54599
          have b7e54630 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e143
               have i₂ := b7e54618
               grind)
            | exact superpose b7e54618 b7e143
            | exact resolve b7e143 b7e54618
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143 b7e54618
          have b7e54758 : (σ x) = (σ y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e54630
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e54630
            | exact resolve b7e54630 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54630
          have b7e54775 : y = (M.op y y) := by
            first
            | (have r₁ := b7e54758
               have r₂ := b7e23
               grind)
            | exact resolve b7e54758 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54758
          have b7e54962 : (σ y) = (M.op x x) := by
            first
            | (have i₁ := b7e295
               have i₂ := b7e54775
               grind)
            | exact superpose b7e54775 b7e295
            | exact resolve b7e295 b7e54775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e295
          have b7e54963 : y = (σ y) := by
            first
            | (have i₁ := b7e2673
               have i₂ := b7e54775
               grind)
            | exact superpose b7e54775 b7e2673
            | exact resolve b7e2673 b7e54775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2673
          have b7e55057 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e4176 X0 y y
               have i₂ := b7e54775
               grind)
            | exact superpose b7e54775 b7e4176
            | exact resolve b7e4176 b7e54775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4176 b7e54775
          have b7e55130 : (σ y) = (M.op y x) := by
            first
            | (have i₁ := b7e54962
               have i₂ := b7e55057 x
               grind)
            | exact superpose b7e55057 b7e54962
            | exact resolve b7e54962 b7e55057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54962 b7e55057
          have b7e55175 : x = (σ y) := by
            first
            | (have i₁ := b7e55130
               have i₂ := b7e2712
               grind)
            | exact superpose b7e2712 b7e55130
            | exact resolve b7e55130 b7e2712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2712 b7e55130
          have b7e55210 : x = y := by
            first
            | (have i₁ := b7e55175
               have i₂ := b7e54963
               grind)
            | exact superpose b7e54963 b7e55175
            | exact resolve b7e55175 b7e54963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54963 b7e55175
          have b7e55237 : False := by grind
          exact b7e55237
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e821 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e60 x y
               grind)
            | exact superpose b8e60 b8e20
            | (have j1 := b8e60 x y
               grind)
            | exact resolve b8e20 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e880 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e821
               have r₂ := b8e24
               grind)
            | exact resolve b8e821 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e821
          have b8e889 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e880
               have r₂ := b8e23
               grind)
            | exact resolve b8e880 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e880
          have b8e894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e889
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e889
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e889
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e889
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e889 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e889
          have b8e895 : y = (M.op y x) ∨ x = y := by grind
          clear b8e894
          have b8e896 : x = y := by
            first
            | (have r₁ := b8e895
               have r₂ := b8e22
               grind)
            | exact resolve b8e895 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e895
          have b8e897 : False := by grind
          exact b8e897

/-- `Equation4416`: `x ◇ (x ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation4416 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4416 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4416.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e34 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e35 (M.op x X0)
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e35
        | exact resolve b0e35 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : y ≠ y ∨ (k x y) = (M.op x x) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : (k x y) = (M.op x x) := by grind
      clear b0e42
      have b0e44 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear b0e40
      have b0e45 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
      have b0e46 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e45
        | exact resolve b0e45 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e45
      have b0e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e74 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x)
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e11
        | exact resolve b0e11 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e74 X0
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e74
        | exact resolve b0e74 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e136 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e34 (σ x)
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e34
        | exact resolve b0e34 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e149 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e136
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e136
        | exact resolve b0e136 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136
      have b0e188 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e34 (σ (M.op x x))
           have i₂ := b0e149
           grind)
        | exact superpose b0e149 b0e34
        | exact resolve b0e34 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e149
      have b0e1024 : (M.op x y) = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b0e37 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e1843 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X1) (σ X0)
           have i₂ := b0e51 X1 X0
           grind)
        | exact superpose b0e51 b0e14
        | (have j0 := b0e14 (σ X1) (σ X0)
           have j1 := b0e51 X1 X0
           grind)
        | (have r₁ := b0e14 (σ X1) (σ X1)
           have r₂ := b0e51 X1 X1
           grind)
        | (have r₁ := b0e14 (σ X0) (σ X1)
           have r₂ := b0e51 X0 X1
           grind)
        | exact resolve b0e14 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e1865 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e1843 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1843
      have b0e1882 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1865 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e1865
        | (have j0 := b0e1865 X0 X1
           grind)
        | exact resolve b0e1865 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1865
      have b0e606185 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e1882 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1882
      have b0e606187 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e606185 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e606185
      have b0e606205 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e606187 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e606187
        | exact resolve b0e606187 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e606187
      have b0e606222 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e606205 X0
           have i₂ := b0e23 X0 (τ X0)
           grind)
        | exact superpose b0e23 b0e606205
        | (have j0 := b0e606205 X0
           grind)
        | exact resolve b0e606205 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e606205
      have b0e606224 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e606222 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e606222
        | (have j0 := b0e606222 X0
           grind)
        | exact resolve b0e606222 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e606222
      have b0e606225 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e606224 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e606224 X0
           have r₂ := b0e14 X0 X0
           grind)
        | exact resolve b0e606224 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e606224
      have b0e607522 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e606225 (σ X0)
           grind)
        | exact superpose b0e606225 b0e17
        | exact resolve b0e17 b0e606225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e607551 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e607522 X0
           have i₂ := b0e606225 X0
           grind)
        | exact superpose b0e606225 b0e607522
        | exact resolve b0e607522 b0e606225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e606225 b0e607522
      have b0e609279 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x x))) := by
        first
        | (have i₁ := b0e79 (σ (M.op x x))
           have i₂ := b0e607551 (M.op x x)
           grind)
        | exact superpose b0e607551 b0e79
        | exact resolve b0e79 b0e607551
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79 b0e607551
      have b0e609518 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op x (M.op x (M.op x x)))) := by
        first
        | (have i₁ := b0e609279
           have i₂ := b0e11 x (M.op x x) x
           grind)
        | exact superpose b0e11 b0e609279
        | exact resolve b0e609279 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e609279
      have b0e609551 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op y (M.op x x))) := by
        first
        | (have i₁ := b0e609518
           have i₂ := b0e35 (M.op x x)
           grind)
        | exact superpose b0e35 b0e609518
        | exact resolve b0e609518 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e609518
      have b0e609569 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x x))) := by
        first
        | (have i₁ := b0e609551
           have i₂ := b0e1024
           grind)
        | exact superpose b0e1024 b0e609551
        | exact resolve b0e609551 b0e1024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1024 b0e609551
      have b0e614123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e188
           have i₂ := b0e609569
           grind)
        | exact superpose b0e609569 b0e188
        | exact resolve b0e188 b0e609569
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e188 b0e609569
      have b0e614200 : False := by grind
      exact b0e614200
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) X0 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b1e41 : (k x y) = (M.op x x) := by grind
        clear b1e40
        have b1e42 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e51 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2 X1
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e17 X0 (M.op X2 X0)
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X1 X0
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X1 (M.op X1 (M.op X2 X1))) = X0 ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 (M.op X2 X1) X2
             have i₂ := b1e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e17 X0 (M.op (M.op X2 X0) X1)
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 (M.op X2 X1) X0
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e66 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e62
             have r₂ := b1e21
             grind)
          | exact resolve b1e62 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e67 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e66
          | exact resolve b1e66 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e68 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e67
          | exact resolve b1e67 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e67
        have b1e71 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e68
             grind)
          | exact superpose b1e68 b1e13
          | exact resolve b1e13 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e72 : y = (M.op x x) := by
          first
          | (have i₁ := b1e71
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e71
          | exact resolve b1e71 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e84 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e33 x
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e33
          | exact resolve b1e33 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e88 : y = (M.op x y) := by
          first
          | (have i₁ := b1e84
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e84
          | exact resolve b1e84 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e135 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b1e33 y
             have i₂ := b1e88
             grind)
          | exact superpose b1e88 b1e33
          | exact resolve b1e33 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e142 : y = (M.op y y) := by
          first
          | (have i₁ := b1e135
             have i₂ := b1e88
             grind)
          | exact superpose b1e88 b1e135
          | exact resolve b1e135 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e135
        have b1e143 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e32 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e32
          | exact resolve b1e32 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e157 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e142
             grind)
          | exact superpose b1e142 b1e15
          | (have r₁ := b1e15 y y
             have r₂ := b1e142
             grind)
          | exact resolve b1e15 b1e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e160 : y = (k y y) := by grind
        clear b1e157
        have b1e1524 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e51 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e1940 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e48 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e48
          | exact resolve b1e48 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2037 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e48 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e2038 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e2037 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2037
        have b1e2048 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b1e1940
        have b1e2073 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e2048
             have r₂ := b1e42
             grind)
          | exact resolve b1e2048 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e2048
        have b1e2155 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e2073
             grind)
          | exact superpose b1e2073 b1e13
          | exact resolve b1e13 b1e2073
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2156 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k x x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 (k x x) X0
             have i₂ := b1e2073
             grind)
          | exact superpose b1e2073 b1e18
          | exact resolve b1e18 b1e2073
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2073
        have b1e2169 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e2156 X0
             have i₂ := b1e18 y X0
             grind)
          | exact superpose b1e18 b1e2156
          | exact resolve b1e2156 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2156
        have b1e2170 : y = (k x x) := by
          first
          | (have i₁ := b1e2155
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e2155
          | exact resolve b1e2155 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2155
        have b1e3692 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op (k x x) X0)) ∨ (M.op (k x x) (k x x)) = X0 ∨ (M.op X0 (k x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2169 X0
             have i₂ := b1e17 (k x x) X0
             grind)
          | exact superpose b1e17 b1e2169
          | (have j1 := b1e17 (k x x) X0
             grind)
          | exact resolve b1e2169 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2169
        have b1e3728 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op (k x x) (k x x)) = X0 ∨ (M.op X0 (k x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3692 X0
             have i₂ := b1e2170
             grind)
          | exact superpose b1e2170 b1e3692
          | (have j0 := b1e3692 X0
             grind)
          | exact resolve b1e3692 b1e2170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3692
        have b1e3736 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 (k x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3728 X0
             have i₂ := b1e2170
             grind)
          | exact superpose b1e2170 b1e3728
          | (have j0 := b1e3728 X0
             grind)
          | exact resolve b1e3728 b1e2170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3728
        have b1e3743 : ∀ X0 : G, y = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 (k x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3736 X0
             have i₂ := b1e142
             grind)
          | exact superpose b1e142 b1e3736
          | (have j0 := b1e3736 X0
             grind)
          | exact resolve b1e3736 b1e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e142 b1e3736
        have b1e3749 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = X0 ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3743 X0
             have i₂ := b1e2170
             grind)
          | exact superpose b1e2170 b1e3743
          | (have j0 := b1e3743 X0
             grind)
          | exact resolve b1e3743 b1e2170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2170 b1e3743
        have b1e8203 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e2038 y
             have i₂ := b1e160
             grind)
          | exact superpose b1e160 b1e2038
          | (have j0 := b1e2038 y
             grind)
          | exact resolve b1e2038 b1e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160 b1e2038
        have b1e8211 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e8203
        have b1e8334 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ y) (M.op (σ y) (σ y))) = X0 ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e53 X0 (σ y) (σ y)
             have i₂ := b1e8211
             grind)
          | exact superpose b1e8211 b1e53
          | exact resolve b1e53 b1e8211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e8353 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b1e8334 X0
             have j1 := b1e1524 X0 (σ y)
             grind)
          | (have r₁ := b1e8334 (M.op (σ y) (σ y))
             have r₂ := b1e1524 (k (σ y) (M.op (σ y) (σ y))) (σ y)
             grind)
          | (have r₁ := b1e8334 X0
             have r₂ := b1e1524 X0 (σ y)
             grind)
          | (have r₁ := b1e8334 (M.op x (M.op x x))
             have r₂ := b1e1524 (M.op (σ y) (M.op (σ y) (σ y))) x
             grind)
          | exact resolve b1e8334 b1e1524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1524 b1e8334
        have b1e130019 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e8353 (σ X0)
             grind)
          | exact superpose b1e8353 b1e18
          | (have j1 := b1e8353 (σ X0)
             grind)
          | exact resolve b1e18 b1e8353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8353
        have b1e422713 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e143
             have i₂ := b1e130019 x
             grind)
          | exact superpose b1e130019 b1e143
          | (have j1 := b1e130019 x
             grind)
          | exact resolve b1e143 b1e130019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e130019
        have b1e504011 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e422713
             grind)
          | exact superpose b1e422713 b1e21
          | exact resolve b1e21 b1e422713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422713
        have b1e507875 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e504011
             have i₂ := b1e3749 x
             grind)
          | exact superpose b1e3749 b1e504011
          | (have j1 := b1e3749 x
             grind)
          | exact resolve b1e504011 b1e3749
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3749 b1e504011
        have b1e507876 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e507875
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e507875
          | exact resolve b1e507875 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e507875
        have b1e507877 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
        clear b1e507876
        have b1e507882 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e507877
             have i₂ := b1e88
             grind)
          | exact superpose b1e88 b1e507877
          | exact resolve b1e507877 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88 b1e507877
        have b1e507883 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
        clear b1e507882
        have b1e511739 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e28 (σ y)
             have i₂ := b1e507883
             grind)
          | exact superpose b1e507883 b1e28
          | exact resolve b1e28 b1e507883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e507883
        have b1e512020 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e511739
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e511739
          | exact resolve b1e511739 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e511739
        have b1e512090 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e512020
             have i₂ := b1e143
             grind)
          | exact superpose b1e143 b1e512020
          | exact resolve b1e512020 b1e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e143 b1e512020
        have b1e512109 : x = y := by
          first
          | (have r₁ := b1e512090
             have r₂ := b1e21
             grind)
          | exact resolve b1e512090 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e512090
        have b1e515202 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e512109
             grind)
          | exact superpose b1e512109 b1e21
          | exact resolve b1e21 b1e512109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e512109
        have b1e515300 : False := by grind
        exact b1e515300
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b2e30 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
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
        have b2e31 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 (M.op x X0)
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e30 (M.op x X0)
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e30
          | exact resolve b2e30 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b2e38 : (k x y) = (M.op x x) := by grind
        clear b2e37
        have b2e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e46 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 X1
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 X0 (M.op X2 X0)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X1 (M.op X1 (M.op X2 X1))) = X0 ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (M.op X2 X1) X2
             have i₂ := b2e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 X0 (M.op (M.op X2 X0) X1)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 (M.op X2 X1) X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e139 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b2e31 y x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31
          | exact resolve b2e31 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e170 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e139 X0
             have i₂ := b2e12 y X0 y
             grind)
          | exact superpose b2e12 b2e139
          | exact resolve b2e139 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e172 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e170 X0
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e170
          | exact resolve b2e170 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e170
        have b2e173 : y = (M.op y y) := by
          first
          | (have i₁ := b2e172 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e172
          | exact resolve b2e172 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172
        have b2e282 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b2e15 y y
             have i₂ := b2e173
             grind)
          | exact superpose b2e173 b2e15
          | (have r₁ := b2e15 y y
             have r₂ := b2e173
             grind)
          | exact resolve b2e15 b2e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e289 : y = (k y y) := by grind
        clear b2e282
        have b2e694 : (M.op x y) = (M.op y (M.op x y)) := by
          first
          | (have i₁ := b2e33 y
             have i₂ := b2e173
             grind)
          | exact superpose b2e173 b2e33
          | exact resolve b2e33 b2e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e749 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e49 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e750 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e749
             have r₂ := b2e21
             grind)
          | exact resolve b2e749 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e749
        have b2e751 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e750
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e750
          | exact resolve b2e750 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e750
        have b2e752 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e751
             have i₂ := b2e38
             grind)
          | exact superpose b2e38 b2e751
          | exact resolve b2e751 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e751
        have b2e896 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e752
             grind)
          | exact superpose b2e752 b2e19
          | exact resolve b2e19 b2e752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1050 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e46 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e1418 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e43 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e1419 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e1418 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1418
        have b2e1956 : ∀ X0 : G, (M.op y (M.op y y)) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e48 X0 y y
             have i₂ := b2e173
             grind)
          | exact superpose b2e173 b2e48
          | exact resolve b2e48 b2e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e173
        have b2e2086 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e1956 X0
             have j1 := b2e1050 X0 y
             grind)
          | (have r₁ := b2e1956 X0
             have r₂ := b2e1050 X0 y
             grind)
          | (have r₁ := b2e1956 (M.op x (M.op x x))
             have r₂ := b2e1050 (M.op y (M.op y y)) x
             grind)
          | (have r₁ := b2e1956 (M.op y y)
             have r₂ := b2e1050 (k y (M.op y y)) y
             grind)
          | exact resolve b2e1956 b2e1050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1956
        have b2e2169 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e2086 (τ X0)
             grind)
          | exact superpose b2e2086 b2e25
          | (have j1 := b2e2086 (τ X0)
             grind)
          | exact resolve b2e25 b2e2086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e2086
        have b2e6736 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1419 y
             have i₂ := b2e289
             grind)
          | exact superpose b2e289 b2e1419
          | (have j0 := b2e1419 y
             grind)
          | exact resolve b2e1419 b2e289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e289 b2e1419
        have b2e6741 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e6736
        have b2e6775 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ y) (M.op (σ y) (σ y))) = X0 ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e48 X0 (σ y) (σ y)
             have i₂ := b2e6741
             grind)
          | exact superpose b2e6741 b2e48
          | exact resolve b2e48 b2e6741
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e6741
        have b2e6800 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e6775 X0
             have j1 := b2e1050 X0 (σ y)
             grind)
          | (have r₁ := b2e6775 (M.op (σ y) (σ y))
             have r₂ := b2e1050 (k (σ y) (M.op (σ y) (σ y))) (σ y)
             grind)
          | (have r₁ := b2e6775 X0
             have r₂ := b2e1050 X0 (σ y)
             grind)
          | (have r₁ := b2e6775 (M.op x (M.op x x))
             have r₂ := b2e1050 (M.op (σ y) (M.op (σ y) (σ y))) x
             grind)
          | exact resolve b2e6775 b2e1050
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1050 b2e6775
        have b2e142077 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e18 y X0
             have i₂ := b2e6800 (σ X0)
             grind)
          | exact superpose b2e6800 b2e18
          | (have j1 := b2e6800 (σ X0)
             grind)
          | exact resolve b2e18 b2e6800
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6800
        have b2e334010 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e2169 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e2169
          | exact resolve b2e2169 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2169
        have b2e334021 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e334010 X0
             have i₂ := b2e18 y X0
             grind)
          | exact superpose b2e18 b2e334010
          | (have j0 := b2e334010 X0
             grind)
          | exact resolve b2e334010 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e334010
        have b2e459106 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e752
             have i₂ := b2e142077 x
             grind)
          | exact superpose b2e142077 b2e752
          | (have j1 := b2e142077 x
             grind)
          | exact resolve b2e752 b2e142077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e752 b2e142077
        have b2e463011 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e459106
             grind)
          | exact superpose b2e459106 b2e21
          | exact resolve b2e21 b2e459106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e459106
        have b2e466974 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e463011
             have i₂ := b2e334021 x
             grind)
          | exact superpose b2e334021 b2e463011
          | (have j1 := b2e334021 x
             grind)
          | exact resolve b2e463011 b2e334021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e334021 b2e463011
        have b2e466975 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e466974
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e466974
          | exact resolve b2e466974 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e466974
        have b2e466976 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
        clear b2e466975
        have b2e470760 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e13 (M.op x x)
             have i₂ := b2e466976
             grind)
          | exact superpose b2e466976 b2e13
          | exact resolve b2e13 b2e466976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e466976
        have b2e470794 : x = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e470760
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e470760
          | exact resolve b2e470760 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e470760
        have b2e473759 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e30 x
             have i₂ := b2e470794
             grind)
          | exact superpose b2e470794 b2e30
          | exact resolve b2e30 b2e470794
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e474103 : y = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e473759
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e473759
          | exact resolve b2e473759 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e473759
        have b2e481810 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e470794
             have i₂ := b2e474103
             grind)
          | exact superpose b2e474103 b2e470794
          | exact resolve b2e470794 b2e474103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e470794 b2e474103
        have b2e482049 : x = (M.op x y) ∨ x = y := by grind
        clear b2e481810
        have b2e485709 : x = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b2e694
             have i₂ := b2e482049
             grind)
          | exact superpose b2e482049 b2e694
          | exact resolve b2e694 b2e482049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e694 b2e482049
        have b2e486162 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e485709
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e485709
          | exact resolve b2e485709 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e485709
        have b2e486163 : x = y := by grind
        clear b2e486162
        have b2e489896 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e896
             have i₂ := b2e486163
             grind)
          | exact superpose b2e486163 b2e896
          | exact resolve b2e896 b2e486163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e896 b2e486163
        have b2e489956 : False := by grind
        exact b2e489956
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e33 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e33
          | exact resolve b3e33 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b3e42 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e39
        have b3e43 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e55 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 X1
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op X2 X0)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X1 (M.op X1 (M.op X2 X1))) = X0 ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 (M.op X2 X1) X2
             have i₂ := b3e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X2 X0) X1)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 (M.op X2 X1) X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : y = (k x y) ∨ y = (M.op y x) := by grind
        have b3e62 : y = (k x y) := by
          first
          | (have r₁ := b3e60
             have r₂ := b3e20
             grind)
          | exact resolve b3e60 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e163 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b3e32 (σ x)
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e32
          | exact resolve b3e32 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e176 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e163
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e163
          | exact resolve b3e163 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e163
        have b3e177 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e176
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e176
          | exact resolve b3e176 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e176
        have b3e178 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e177
             grind)
          | exact superpose b3e177 b3e19
          | exact resolve b3e19 b3e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e179 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e32 (σ y)
             have i₂ := b3e177
             grind)
          | exact superpose b3e177 b3e32
          | exact resolve b3e32 b3e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e187 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e179
             have i₂ := b3e177
             grind)
          | exact superpose b3e177 b3e179
          | exact resolve b3e179 b3e177
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e179
        have b3e188 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b3e178
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e178
          | exact resolve b3e178 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e178
        have b3e311 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e187
             grind)
          | exact superpose b3e187 b3e15
          | (have r₁ := b3e15 (σ y) (σ y)
             have r₂ := b3e187
             grind)
          | exact resolve b3e15 b3e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e315 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e311
        have b3e316 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e315
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e315
          | exact resolve b3e315 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e315
        have b3e487 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e316
             grind)
          | exact superpose b3e316 b3e13
          | exact resolve b3e13 b3e316
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e316
        have b3e489 : y = (k y y) := by
          first
          | (have i₁ := b3e487
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e487
          | exact resolve b3e487 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e487
        have b3e708 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e489
             grind)
          | exact superpose b3e489 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e489
        have b3e709 : y = (M.op y y) := by grind
        clear b3e708
        have b3e1476 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e55 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e2019 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e177
             have i₂ := b3e53 y x
             grind)
          | exact superpose b3e53 b3e177
          | (have j1 := b3e53 y x
             grind)
          | exact resolve b3e177 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e177
        have b3e2072 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e2019
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e2019
          | exact resolve b3e2019 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2019
        have b3e2111 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2072
             have i₂ := b3e187
             grind)
          | exact superpose b3e187 b3e2072
          | exact resolve b3e2072 b3e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e187 b3e2072
        have b3e2112 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
        clear b3e2111
        have b3e2290 : ∀ X0 : G, (M.op y (M.op y y)) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e57 X0 y y
             have i₂ := b3e709
             grind)
          | exact superpose b3e709 b3e57
          | exact resolve b3e57 b3e709
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e2423 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e2290 X0
             have j1 := b3e1476 X0 y
             grind)
          | (have r₁ := b3e2290 X0
             have r₂ := b3e1476 X0 y
             grind)
          | (have r₁ := b3e2290 (M.op x (M.op x x))
             have r₂ := b3e1476 (M.op y (M.op y y)) x
             grind)
          | (have r₁ := b3e2290 (M.op y y)
             have r₂ := b3e1476 (k y (M.op y y)) y
             grind)
          | exact resolve b3e2290 b3e1476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1476 b3e2290
        have b3e4997 : (σ y) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b3e2112
             have i₂ := b3e2423 x
             grind)
          | exact superpose b3e2423 b3e2112
          | (have j1 := b3e2423 x
             grind)
          | exact resolve b3e2112 b3e2423
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2112 b3e2423
        have b3e5009 : (σ x) = (σ y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b3e4997
             have r₂ := b3e188
             grind)
          | exact resolve b3e4997 b3e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4997
        have b3e5013 : x = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e5009
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e5009
          | exact resolve b3e5009 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e5009
        have b3e5089 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 y
             have i₂ := b3e5013
             grind)
          | exact superpose b3e5013 b3e12
          | exact resolve b3e12 b3e5013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5013
        have b3e5121 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e5089 X0
             have i₂ := b3e33 X0
             grind)
          | exact superpose b3e33 b3e5089
          | exact resolve b3e5089 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e5089
        have b3e5722 : y = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e5121 x
             grind)
          | exact superpose b3e5121 b3e21
          | exact resolve b3e21 b3e5121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5121
        have b3e5728 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e5722
             have r₂ := b3e20
             grind)
          | exact resolve b3e5722 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5722
        have b3e5891 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e5728
             grind)
          | exact superpose b3e5728 b3e13
          | exact resolve b3e13 b3e5728
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5728
        have b3e5925 : x = y := by
          first
          | (have i₁ := b3e5891
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e5891
          | exact resolve b3e5891 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5891
        have b3e6271 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e188
             have i₂ := b3e5925
             grind)
          | exact superpose b3e5925 b3e188
          | exact resolve b3e188 b3e5925
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e188 b3e5925
        have b3e6290 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e6271
             have i₂ := b3e709
             grind)
          | exact superpose b3e709 b3e6271
          | exact resolve b3e6271 b3e709
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e709 b3e6271
        have b3e6291 : False := by grind
        exact b3e6291
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X2)) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op X1 X2) X3
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 X0) X1 X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op x X0)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op (M.op X1 X2) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X1 X2) X3) X1
               have i₂ := b4e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e39 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e39 (M.op x X0)
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e39
            | exact resolve b4e39 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 y
               have i₂ := b4e41
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e51 X0
               have i₂ := b4e13 y X0 x
               grind)
            | exact superpose b4e13 b4e51
            | exact resolve b4e51 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e54 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e52 X0
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e52
            | exact resolve b4e52 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e62 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 X1
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X2 X0)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X2 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 X1 X3 (M.op x X0)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e163 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e164 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e38 (M.op (σ x) X0)
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e203 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
            first
            | (have i₁ := b4e34 (M.op x (σ x))
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e214 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (M.op x (σ x))
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e221 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e214 X0
               have i₂ := b4e13 (σ y) X0 (σ x)
               grind)
            | exact superpose b4e13 b4e214
            | exact resolve b4e214 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214
          have b4e227 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e203
               have i₂ := b4e13 (σ y) (σ x) (σ x)
               grind)
            | exact superpose b4e13 b4e203
            | exact resolve b4e203 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e203
          have b4e229 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e221 X0
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e221
            | exact resolve b4e221 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e221
          have b4e233 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e227
               have i₂ := b4e163
               grind)
            | exact superpose b4e163 b4e227
            | exact resolve b4e227 b4e163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227
          have b4e234 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b4e233
               have i₂ := b4e164 (σ y)
               grind)
            | exact superpose b4e164 b4e233
            | exact resolve b4e233 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e233
          have b4e469 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X0 (M.op X0 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op X0 X2) x
               have i₂ := b4e32 X1 X0 X2 x
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e588 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e163
               grind)
            | exact superpose b4e163 b4e23
            | exact resolve b4e23 b4e163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e591 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ x) X0
               have i₂ := b4e163
               grind)
            | exact superpose b4e163 b4e13
            | exact resolve b4e13 b4e163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e607 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e591 X0
               have i₂ := b4e164 (σ y)
               grind)
            | exact superpose b4e164 b4e591
            | exact resolve b4e591 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e164 b4e591
          have b4e616 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e607 X0
               have i₂ := b4e234
               grind)
            | exact superpose b4e234 b4e607
            | exact resolve b4e607 b4e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e234 b4e607
          have b4e717 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 X0 X1 X2
               have i₂ := b4e33 X1 X2 X0 X0
               grind)
            | exact superpose b4e33 b4e37
            | exact resolve b4e37 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e37
          have b4e1520 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X1 (M.op X1 (M.op (M.op X3 X1) X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e40 X3 X3 X1 X2
               have i₂ := b4e117 X3 X1 X0 X2
               grind)
            | exact superpose b4e117 b4e40
            | exact resolve b4e40 b4e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e117
          have b4e2395 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e62 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62
          have b4e20715 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1520 X2 X0 X1 x
               have i₂ := b4e469 X0 x X1
               grind)
            | exact superpose b4e469 b4e1520
            | exact resolve b4e1520 b4e469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e469 b4e1520
          have b4e144020 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e2395 X0 (σ y)
               have i₂ := b4e229 (σ y)
               grind)
            | exact superpose b4e229 b4e2395
            | (have j0 := b4e2395 X0 (σ y)
               grind)
            | (have r₁ := b4e2395 (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) (σ y)
               have r₂ := b4e229 (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b4e2395 (M.op (σ y) (σ y)) (σ y)
               have r₂ := b4e229 (σ y)
               grind)
            | exact resolve b4e2395 b4e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229
          have b4e144022 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e2395 X0 y
               have i₂ := b4e54 y
               grind)
            | exact superpose b4e54 b4e2395
            | (have j0 := b4e2395 X0 y
               grind)
            | (have r₁ := b4e2395 (M.op y (M.op y (M.op y y))) y
               have r₂ := b4e54 (M.op y y)
               grind)
            | (have r₁ := b4e2395 (M.op y y) y
               have r₂ := b4e54 y
               grind)
            | exact resolve b4e2395 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2395
          have b4e144026 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b4e144022 X0
               have j1 := b4e18 y X0
               grind)
            | (have r₁ := b4e144022 (k y y)
               have r₂ := b4e18 y y
               grind)
            | (have r₁ := b4e144022 x
               have r₂ := b4e18 y x
               grind)
            | (have r₁ := b4e144022 (M.op X0 X0)
               have r₂ := b4e18 X0 (M.op y y)
               grind)
            | exact resolve b4e144022 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144022
          have b4e144028 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b4e144020 X0
               have j1 := b4e18 (σ y) X0
               grind)
            | (have r₁ := b4e144020 (k (σ y) (σ y))
               have r₂ := b4e18 (σ y) (σ y)
               grind)
            | (have r₁ := b4e144020 x
               have r₂ := b4e18 (σ y) x
               grind)
            | (have r₁ := b4e144020 (M.op X0 X0)
               have r₂ := b4e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact resolve b4e144020 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144020
          have b4e144113 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b4e27 X0 y
               have i₂ := b4e144026 (τ X0)
               grind)
            | exact superpose b4e144026 b4e27
            | (have j1 := b4e144026 (τ X0)
               grind)
            | exact resolve b4e27 b4e144026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e144026
          have b4e144267 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e144028 (σ X0)
               grind)
            | exact superpose b4e144028 b4e19
            | (have j1 := b4e144028 (σ X0)
               grind)
            | exact resolve b4e19 b4e144028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144028
          have b4e331180 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e144113 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e144113
            | exact resolve b4e144113 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144113
          have b4e331191 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e331180 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e331180
            | (have j0 := b4e331180 X0
               grind)
            | exact resolve b4e331180 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e331180
          have b4e413061 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e163
               have i₂ := b4e144267 x
               grind)
            | exact superpose b4e144267 b4e163
            | (have j1 := b4e144267 x
               grind)
            | exact resolve b4e163 b4e144267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163 b4e144267
          have b4e420719 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e413061
               grind)
            | exact superpose b4e413061 b4e20
            | exact resolve b4e20 b4e413061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e413061
          have b4e421904 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e420719
               have i₂ := b4e331191 x
               grind)
            | exact superpose b4e331191 b4e420719
            | (have j1 := b4e331191 x
               grind)
            | exact resolve b4e420719 b4e331191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e331191 b4e420719
          have b4e421905 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e421904
               have i₂ := b4e41
               grind)
            | exact superpose b4e41 b4e421904
            | exact resolve b4e421904 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e421904
          have b4e421906 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e421905
          have b4e423854 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e588
               have i₂ := b4e421906
               grind)
            | exact superpose b4e421906 b4e588
            | exact resolve b4e588 b4e421906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e588
          have b4e423862 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e616 (σ x)
               have i₂ := b4e421906
               grind)
            | exact superpose b4e421906 b4e616
            | exact resolve b4e616 b4e421906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e616 b4e421906
          have b4e424064 : (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e423862
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e423862
            | exact resolve b4e423862 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e423862
          have b4e424147 : x = (M.op x y) := by
            first
            | (have r₁ := b4e424064
               have r₂ := b4e423854
               grind)
            | exact resolve b4e424064 b4e423854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e423854 b4e424064
          have b4e427728 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b4e39 y
               have i₂ := b4e424147
               grind)
            | exact superpose b4e424147 b4e39
            | exact resolve b4e39 b4e424147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e427882 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b4e717 x y X0
               have i₂ := b4e424147
               grind)
            | exact superpose b4e424147 b4e717
            | exact resolve b4e717 b4e424147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e717
          have b4e428025 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op x (M.op x (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e20715 x y X0
               have i₂ := b4e424147
               grind)
            | exact superpose b4e424147 b4e20715
            | exact resolve b4e20715 b4e424147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20715 b4e424147
          have b4e428098 : ∀ X0 : G, (M.op y (M.op x x)) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b4e428025 X0
               have i₂ := b4e39 (M.op x x)
               grind)
            | exact superpose b4e39 b4e428025
            | exact resolve b4e428025 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428025
          have b4e428228 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e427882 X0
               have i₂ := b4e54 X0
               grind)
            | exact superpose b4e54 b4e427882
            | exact resolve b4e427882 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54 b4e427882
          have b4e428345 : y = (M.op y y) := by
            first
            | (have i₁ := b4e427728
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e427728
            | exact resolve b4e427728 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e427728
          have b4e428382 : (M.op x (M.op x y)) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b4e428098 x
               have i₂ := b4e13 x y x
               grind)
            | exact superpose b4e13 b4e428098
            | exact resolve b4e428098 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428098
          have b4e428639 : (M.op x (M.op x y)) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e428382
               have i₂ := b4e42 x
               grind)
            | exact superpose b4e42 b4e428382
            | exact resolve b4e428382 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e428382
          have b4e428853 : (M.op y x) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e428639
               have i₂ := b4e428228 x
               grind)
            | exact superpose b4e428228 b4e428639
            | exact resolve b4e428639 b4e428228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428228 b4e428639
          have b4e429013 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b4e428853
               have i₂ := b4e39 y
               grind)
            | exact superpose b4e39 b4e428853
            | exact resolve b4e428853 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e428853
          have b4e429146 : y = (M.op y x) := by
            first
            | (have i₁ := b4e429013
               have i₂ := b4e428345
               grind)
            | exact superpose b4e428345 b4e429013
            | exact resolve b4e429013 b4e428345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428345 b4e429013
          have b4e429260 : False := by grind
          exact b4e429260
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e63 : y = (k x y) ∨ y = (M.op y x) := by grind
          have b5e67 : y = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e1371 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e60 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e1372 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1371
               have r₂ := b5e23
               grind)
            | exact resolve b5e1371 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1371
          have b5e1373 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1372
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1372
            | exact resolve b5e1372 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1372
          have b5e1374 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1373
               have i₂ := b5e67
               grind)
            | exact superpose b5e67 b5e1373
            | exact resolve b5e1373 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e1373
          have b5e2224 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e54 x x
               grind)
            | exact superpose b5e54 b5e24
            | (have j1 := b5e54 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e54 x y
               grind)
            | exact resolve b5e24 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e2328 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e2224
          have b5e7265 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e2328
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e2328
            | (have j1 := b5e18 (σ x) (σ x)
               grind)
            | exact resolve b5e2328 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2328
          have b5e7266 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e7265
          have b5e7267 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e7266
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7266
            | exact resolve b5e7266 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7266
          have b5e7268 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e7267
          have b5e7274 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e7268
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e7268
            | exact resolve b5e7268 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7268
          have b5e7317 : (σ x) ≠ (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e7274
               grind)
            | exact superpose b5e7274 b5e24
            | exact resolve b5e24 b5e7274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7325 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e16 (σ x) (σ x)
               have i₂ := b5e7274
               grind)
            | exact superpose b5e7274 b5e16
            | (have r₁ := b5e16 (σ x) (σ x)
               have r₂ := b5e7274
               grind)
            | exact resolve b5e16 b5e7274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7274
          have b5e7356 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
          clear b5e7325
          have b5e7361 : (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e7356
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e7356
            | exact resolve b5e7356 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7356
          have b5e8203 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e7361
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e7361
            | (have j1 := b5e18 x x
               grind)
            | exact resolve b5e7361 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7361
          have b5e8225 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
          clear b5e8203
          have b5e8240 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e8225
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e8225
            | exact resolve b5e8225 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8225
          have b5e8245 : x = y ∨ x = (M.op x x) := by
            first
            | (have r₁ := b5e8240
               have r₂ := b5e7317
               grind)
            | exact resolve b5e8240 b5e7317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7317 b5e8240
          have b5e8250 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e8245
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e8245
            | exact resolve b5e8245 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8245
          have b5e8251 : x = y := by grind
          clear b5e8250
          have b5e9033 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e8251
               grind)
            | exact superpose b5e8251 b5e23
            | exact resolve b5e23 b5e8251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e9045 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1374
               have i₂ := b5e8251
               grind)
            | exact superpose b5e8251 b5e1374
            | exact resolve b5e1374 b5e8251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1374 b5e8251
          have b5e9061 : False := by grind
          exact b5e9061
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X2 X0) X1 X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X2 X3
             have i₂ := b6e12 X1 X2 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 (M.op x X0)
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e41 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
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
        have b6e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e58 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 X1
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e17 X0 (M.op X2 X0)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 X1 X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X1 (M.op X1 (M.op X2 X1))) = X0 ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 (M.op X2 X1) X2
             have i₂ := b6e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e17 X0 (M.op (M.op X2 X0) X1)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 (M.op X2 X1) X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e15
          | exact resolve b6e15 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e67 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e63
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e63
          | exact resolve b6e63 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e98 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X0 (σ x) X1 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e141 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b6e31 (σ x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e31
          | exact resolve b6e31 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e154 : (σ y) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b6e141
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e141
          | exact resolve b6e141 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e156 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e31 (σ (k x y))
             have i₂ := b6e154
             grind)
          | exact superpose b6e154 b6e31
          | exact resolve b6e31 b6e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e177 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ y) (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) X0 (M.op x (σ y))
             have i₂ := b6e26 x
             grind)
          | exact superpose b6e26 b6e12
          | exact resolve b6e12 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e182 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b6e177 X0
             have i₂ := b6e12 (σ y) X0 (σ y)
             grind)
          | exact superpose b6e12 b6e177
          | exact resolve b6e177 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e177
        have b6e187 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b6e182 X0
             have i₂ := b6e31 X0
             grind)
          | exact superpose b6e31 b6e182
          | exact resolve b6e182 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e182
        have b6e256 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X3 (M.op X2 X0)) X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e29 X2 (M.op X2 X0) X1 X3
             have i₂ := b6e32 X2 X0 X1
             grind)
          | exact superpose b6e32 b6e29
          | exact resolve b6e29 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e258 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op X0 (σ y))) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e26 (M.op x (M.op x X0))
             have i₂ := b6e32 x X0 (σ y)
             grind)
          | exact superpose b6e32 b6e26
          | exact resolve b6e26 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e259 : (M.op (σ y) (M.op (σ y) (σ x))) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e258 x
             have i₂ := b6e32 x (σ y) (σ x)
             grind)
          | exact superpose b6e32 b6e258
          | exact resolve b6e258 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e258
        have b6e265 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e259
             have i₂ := b6e187 (σ x)
             grind)
          | exact superpose b6e187 b6e259
          | exact resolve b6e259 b6e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e187 b6e259
        have b6e269 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e265
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e265
          | exact resolve b6e265 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e265
        have b6e278 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e269
             grind)
          | exact superpose b6e269 b6e15
          | (have r₁ := b6e15 (σ y) (σ y)
             have r₂ := b6e269
             grind)
          | exact resolve b6e15 b6e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e282 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b6e278
        have b6e283 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e282
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e282
          | exact resolve b6e282 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e282
        have b6e421 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e283
             grind)
          | exact superpose b6e283 b6e13
          | exact resolve b6e13 b6e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e283
        have b6e423 : y = (k y y) := by
          first
          | (have i₁ := b6e421
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e421
          | exact resolve b6e421 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e421
        have b6e468 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ x))) (σ (k x y))) = (M.op (M.op X1 (σ x)) (M.op (σ x) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 (σ x) (σ (k x y)) X1 X0
             have i₂ := b6e154
             grind)
          | exact superpose b6e154 b6e28
          | exact resolve b6e28 b6e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e154
        have b6e557 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ x))) (σ (k x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e468 X0 X1
             have i₂ := b6e98 X1 (M.op (σ x) (σ y))
             grind)
          | exact superpose b6e98 b6e468
          | exact resolve b6e468 b6e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e98 b6e468
        have b6e575 : (M.op (σ x) (M.op (σ x) (σ (k x y)))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e557 x x
             have i₂ := b6e256 (σ x) (σ (k x y)) x x
             grind)
          | exact superpose b6e256 b6e557
          | exact resolve b6e557 b6e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e256 b6e557
        have b6e585 : (M.op (σ y) (σ (k x y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e575
             have i₂ := b6e31 (σ (k x y))
             grind)
          | exact superpose b6e31 b6e575
          | exact resolve b6e575 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31 b6e575
        have b6e592 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e585
             have i₂ := b6e156
             grind)
          | exact superpose b6e156 b6e585
          | exact resolve b6e585 b6e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e156 b6e585
        have b6e598 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e423
             grind)
          | exact superpose b6e423 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e423
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e423
        have b6e599 : y = (M.op y y) := by grind
        clear b6e598
        have b6e789 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 y
             have i₂ := b6e599
             grind)
          | exact superpose b6e599 b6e12
          | exact resolve b6e12 b6e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1373 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e58 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e1946 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54 x x
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e54
          | exact resolve b6e54 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e2057 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
        clear b6e1946
        have b6e2088 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e2057
             have r₂ := b6e67
             grind)
          | exact resolve b6e2057 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67 b6e2057
        have b6e2133 : (k x x) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e2088
             grind)
          | exact superpose b6e2088 b6e13
          | exact resolve b6e13 b6e2088
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2088
        have b6e2153 : (k x y) = (k x x) := by
          first
          | (have i₁ := b6e2133
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e2133
          | exact resolve b6e2133 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2133
        have b6e2214 : (M.op x x) = (k x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e2153
             grind)
          | exact superpose b6e2153 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e2153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2153
        have b6e2215 : (M.op x x) = (k x y) ∨ x = (M.op x x) := by grind
        clear b6e2214
        have b6e2284 : ∀ X0 : G, (M.op y (M.op y y)) = X0 ∨ (k y X0) = (M.op y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e60 X0 y y
             have i₂ := b6e599
             grind)
          | exact superpose b6e599 b6e60
          | exact resolve b6e60 b6e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e2419 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e2284 X0
             have j1 := b6e1373 X0 y
             grind)
          | (have r₁ := b6e2284 X0
             have r₂ := b6e1373 X0 y
             grind)
          | (have r₁ := b6e2284 (M.op x (M.op x x))
             have r₂ := b6e1373 (M.op y (M.op y y)) x
             grind)
          | (have r₁ := b6e2284 (M.op y y)
             have r₂ := b6e1373 (k y (M.op y y)) y
             grind)
          | exact resolve b6e2284 b6e1373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1373 b6e2284
        have b6e3094 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e2215
             grind)
          | exact superpose b6e2215 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e2215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2215
        have b6e3095 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b6e3094
             have r₂ := b6e21
             grind)
          | exact resolve b6e3094 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3094
        have b6e3103 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b6e3095
             have r₂ := b6e20
             grind)
          | exact resolve b6e3095 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3095
        have b6e3448 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
        clear b6e3103
        have b6e9931 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e592
             have i₂ := b6e54 y x
             grind)
          | exact superpose b6e54 b6e592
          | (have j1 := b6e54 y x
             grind)
          | exact resolve b6e592 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e592
        have b6e9990 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e9931
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e9931
          | exact resolve b6e9931 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9931
        have b6e10001 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e9990
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e9990
          | exact resolve b6e9990 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9990
        have b6e10010 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e10001
             have i₂ := b6e269
             grind)
          | exact superpose b6e269 b6e10001
          | exact resolve b6e10001 b6e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10001
        have b6e10011 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
        clear b6e10010
        have b6e10950 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e10011
             grind)
          | exact superpose b6e10011 b6e13
          | exact resolve b6e13 b6e10011
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10011
        have b6e10983 : y = (k y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e10950
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e10950
          | exact resolve b6e10950 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10950
        have b6e11854 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2419 x
             have i₂ := b6e10983
             grind)
          | exact superpose b6e10983 b6e2419
          | (have j0 := b6e2419 x
             grind)
          | exact resolve b6e2419 b6e10983
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2419 b6e10983
        have b6e11861 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e11854
             have r₂ := b6e20
             grind)
          | exact resolve b6e11854 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11854
        have b6e12907 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3448
             have i₂ := b6e11861
             grind)
          | exact superpose b6e11861 b6e3448
          | (have r₁ := b6e3448
             have r₂ := b6e11861
             grind)
          | exact resolve b6e3448 b6e11861
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3448
        have b6e12909 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op y X0)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 x
             have i₂ := b6e11861
             grind)
          | exact superpose b6e11861 b6e12
          | exact resolve b6e12 b6e11861
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e12947 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e12907
        have b6e12980 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e12909 X0
             have i₂ := b6e789 X0
             grind)
          | exact superpose b6e789 b6e12909
          | exact resolve b6e12909 b6e789
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e789 b6e12909
        have b6e14123 : x ≠ y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e12947
             grind)
          | exact superpose b6e12947 b6e21
          | exact resolve b6e21 b6e12947
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12947
        have b6e17625 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e11861
             have i₂ := b6e12980 y
             grind)
          | exact superpose b6e12980 b6e11861
          | exact resolve b6e11861 b6e12980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11861 b6e12980
        have b6e17627 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e17625
        have b6e17631 : x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17627
             have i₂ := b6e599
             grind)
          | exact superpose b6e599 b6e17627
          | exact resolve b6e17627 b6e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17627
        have b6e17668 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e17631
             have r₂ := b6e14123
             grind)
          | exact resolve b6e17631 b6e14123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e14123 b6e17631
        have b6e18746 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e17668
             grind)
          | exact superpose b6e17668 b6e19
          | exact resolve b6e19 b6e17668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e18758 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e17668
             grind)
          | exact superpose b6e17668 b6e13
          | exact resolve b6e13 b6e17668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17668
        have b6e18791 : x = y := by
          first
          | (have i₁ := b6e18758
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e18758
          | exact resolve b6e18758 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18758
        have b6e18795 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e18746
             have i₂ := b6e269
             grind)
          | exact superpose b6e269 b6e18746
          | exact resolve b6e18746 b6e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e269 b6e18746
        have b6e18799 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e18795
             have i₂ := b6e18791
             grind)
          | exact superpose b6e18791 b6e18795
          | exact resolve b6e18795 b6e18791
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e18791 b6e18795
        have b6e18800 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b6e18799
             have i₂ := b6e599
             grind)
          | exact superpose b6e599 b6e18799
          | exact resolve b6e18799 b6e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e599 b6e18799
        have b6e18801 : False := by grind
        exact b6e18801
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e48 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e2640 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e64 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e64
            | exact resolve b7e64 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e2770 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
          clear b7e2640
          have b7e2792 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e2770
               have r₂ := b7e51
               grind)
            | exact resolve b7e2770 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51 b7e2770
          have b7e2827 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e2792
               grind)
            | exact superpose b7e2792 b7e14
            | exact resolve b7e14 b7e2792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2792
          have b7e2842 : y = (k x x) := by
            first
            | (have i₁ := b7e2827
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2827
            | exact resolve b7e2827 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2827
          have b7e2886 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e2842
               grind)
            | exact superpose b7e2842 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e2842
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2887 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e2886
          have b7e2889 : x = (M.op x x) := by
            first
            | (have r₁ := b7e2887
               have r₂ := b7e22
               grind)
            | exact resolve b7e2887 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2887
          have b7e3230 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e2889
               grind)
            | exact superpose b7e2889 b7e22
            | exact resolve b7e22 b7e2889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3233 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b7e16 x x
               have i₂ := b7e2889
               grind)
            | exact superpose b7e2889 b7e16
            | (have r₁ := b7e16 x x
               have r₂ := b7e2889
               grind)
            | exact resolve b7e16 b7e2889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2889
          have b7e3251 : x = (k x x) := by grind
          clear b7e3233
          have b7e3607 : x = y := by
            first
            | (have i₁ := b7e2842
               have i₂ := b7e3251
               grind)
            | exact superpose b7e3251 b7e2842
            | exact resolve b7e2842 b7e3251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2842 b7e3251
          have b7e3619 : False := by grind
          exact b7e3619
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e1146 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e67 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e1147 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1146
               have r₂ := b8e23
               grind)
            | exact resolve b8e1146 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1146
          have b8e1148 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1147
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1147
            | exact resolve b8e1147 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1147
          have b8e1149 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1148
               grind)
            | exact superpose b8e1148 b8e20
            | exact resolve b8e20 b8e1148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1148
          have b8e1218 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1149
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1149
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1149 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1149
          have b8e1219 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1218
          have b8e1221 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1219
               have r₂ := b8e22
               grind)
            | exact resolve b8e1219 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1219
          have b8e1223 : False := by grind
          exact b8e1223
