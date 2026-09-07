import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation4461 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4461 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e28
      have b0e79 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e84 : False := by grind
      exact b0e84
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : False := by grind
        exact b1e28
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : False := by grind
        exact b2e28
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e39 x X1
               have i₂ := b4e40 x X1
               grind)
            | exact superpose b4e40 b4e39
            | exact resolve b4e39 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e69 X0 X1
               have i₂ := b4e31 X1
               grind)
            | exact superpose b4e31 b4e69
            | (have j0 := b4e69 X0 X1
               grind)
            | exact resolve b4e69 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e84 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (M.op X0 X1) X1
               have i₂ := b4e40 X1 X0
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op y (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e40 X0 (σ y)
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e40
            | exact resolve b4e40 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : (M.op y y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e89 x
               have i₂ := b4e40 x y
               grind)
            | exact superpose b4e40 b4e89
            | exact resolve b4e89 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e89
          have b4e138 : (M.op y (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e43 (σ y)
               have i₂ := b4e31 y
               grind)
            | exact superpose b4e31 b4e43
            | exact resolve b4e43 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e43
          have b4e147 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e138
               have i₂ := b4e100
               grind)
            | exact superpose b4e100 b4e138
            | exact resolve b4e138 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100 b4e138
          have b4e2564 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e81 x y
               grind)
            | exact superpose b4e81 b4e20
            | (have j1 := b4e81 x y
               grind)
            | exact resolve b4e20 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e2620 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e2564
               have r₂ := b4e23
               grind)
            | exact resolve b4e2564 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2564
          have b4e2662 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b4e2620
               have i₂ := b4e147
               grind)
            | exact superpose b4e147 b4e2620
            | exact resolve b4e2620 b4e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147 b4e2620
          have b4e8030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e2662
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e2662
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e2662
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e2662
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e2662 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2662
          have b4e8032 : (σ x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b4e8030
          have b4e8037 : (σ x) = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b4e8032
               have r₂ := b4e21
               grind)
            | exact resolve b4e8032 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8032
          have b4e8084 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e84 y y
               have i₂ := b4e8037
               grind)
            | exact superpose b4e8037 b4e84
            | exact resolve b4e84 b4e8037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8037
          have b4e8090 : (σ x) = (σ y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e8084
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e8084
            | exact resolve b4e8084 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8084
          have b4e8110 : x = (M.op y y) := by
            first
            | (have r₁ := b4e8090
               have r₂ := b4e23
               grind)
            | exact resolve b4e8090 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8090
          have b4e8414 : x = (M.op x x) := by
            first
            | (have i₁ := b4e84 y y
               have i₂ := b4e8110
               grind)
            | exact superpose b4e8110 b4e84
            | exact resolve b4e84 b4e8110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84 b4e8110
          have b4e9046 : x = y := by
            first
            | (have i₁ := b4e22
               have i₂ := b4e8414
               grind)
            | exact superpose b4e8414 b4e22
            | exact resolve b4e22 b4e8414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8414
          have b4e9099 : False := by grind
          exact b4e9099
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e147 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e24
            | exact resolve b5e24 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e158 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e147
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e147
            | exact resolve b5e147 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e147
          have b5e159 : False := by grind
          exact b5e159
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : x = y := by
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
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e112 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e24
            | exact resolve b7e24 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e149 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e112
               grind)
            | exact superpose b7e112 b7e14
            | exact resolve b7e14 b7e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e150 : y = (M.op x x) := by
            first
            | (have i₁ := b7e149
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e149
            | exact resolve b7e149 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e149
          have b7e154 : False := by grind
          exact b7e154
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X1 X2) X2 X3
               have i₂ := b8e13 X2 X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op X2 X2) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e13 x X1 X3
               have i₂ := b8e13 x X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e13 X2 X1 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e27
          have b8e45 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e41 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e41
            | exact resolve b8e41 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e46 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e45
          have b8e66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e72 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = X0 := by
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
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (M.op (σ x) (σ x))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ x) (σ x)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e66 X0 X1
               have i₂ := b8e31 X1
               grind)
            | exact superpose b8e31 b8e66
            | (have j0 := b8e66 X0 X1
               grind)
            | exact resolve b8e66 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e85 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e101 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op X1 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e35 X1 X2 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e35
            | exact resolve b8e35 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op X1 X1)
               have i₂ := b8e35 X1 (M.op X1 X1) X0
               grind)
            | (have i₁ := b8e13 X2 X3 (M.op X1 X1)
               have i₂ := b8e35 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b8e35 b8e13
            | exact resolve b8e13 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e134 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e38 X2 X3 (M.op X1 X3)
               have i₂ := b8e38 X3 X1 X0
               grind)
            | (have i₁ := b8e38 X2 X3 (M.op X1 X3)
               have i₂ := b8e38 X0 X1 X3
               grind)
            | exact superpose b8e38 b8e38
            | exact resolve b8e38 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e139 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e38 X2 (M.op X3 X3) X1
               have i₂ := b8e13 X0 X1 X3
               grind)
            | exact superpose b8e13 b8e38
            | exact resolve b8e38 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e140 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X1 (σ X0) (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e38
            | exact resolve b8e38 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X1 X2) X2 X3
               have i₂ := b8e38 X2 X1 X0
               grind)
            | (have i₁ := b8e13 (M.op X1 X2) X2 X3
               have i₂ := b8e38 X0 X1 X2
               grind)
            | exact superpose b8e38 b8e13
            | exact resolve b8e13 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e174 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op (M.op X3 X2) (M.op (M.op X4 X4) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e33 X4 X3 X2 (M.op X1 X1)
               have i₂ := b8e35 X1 (M.op X1 X1) X0
               grind)
            | (have i₁ := b8e33 X4 X3 X2 (M.op X1 X1)
               have i₂ := b8e35 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b8e35 b8e33
            | exact resolve b8e33 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e175 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = (M.op (M.op X3 X2) (M.op (M.op X4 X4) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e33 X4 X3 X2 (M.op X1 X1)
               have i₂ := b8e13 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e176 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 X1) (M.op (M.op X3 X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e33 X3 X2 X1 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e33
            | exact resolve b8e33 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e202 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op X3 X2) (M.op (σ (M.op X0 X0)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e33 (σ X0) X3 X2 X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e33
            | exact resolve b8e33 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e250 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e46 X0
               grind)
            | exact superpose b8e46 b8e14
            | exact resolve b8e14 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e272 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X4 (M.op X5 (M.op X4 X5))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e34 X5 X4 x x
               have i₂ := b8e34 X1 X0 x x
               grind)
            | exact superpose b8e34 b8e34
            | exact resolve b8e34 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e292 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 (σ X0) (σ X0) X2 X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e34
            | exact resolve b8e34 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e301 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 x x X1 X0
               have i₂ := b8e34 x x X3 X2
               grind)
            | exact superpose b8e34 b8e34
            | exact resolve b8e34 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e319 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op x x)
               have i₂ := b8e34 X1 X0 x x
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e35 X2 X3 (M.op x x)
               have i₂ := b8e34 X1 X0 x x
               grind)
            | exact superpose b8e34 b8e35
            | exact resolve b8e35 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e614 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (τ X0)
               have i₂ := b8e250 X0
               grind)
            | exact superpose b8e250 b8e13
            | exact resolve b8e13 b8e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e622 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e35 X1 X2 (τ X0)
               have i₂ := b8e250 X0
               grind)
            | exact superpose b8e250 b8e35
            | exact resolve b8e35 b8e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e656 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X1 X1)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e85 X1 (σ X0) (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e85
            | exact resolve b8e85 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e802 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (σ (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e101 X1 (τ X0) X2
               have i₂ := b8e250 X0
               grind)
            | exact superpose b8e250 b8e101
            | exact resolve b8e101 b8e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101
          have b8e894 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e72 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e895 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e894
               have r₂ := b8e23
               grind)
            | exact resolve b8e894 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e894
          have b8e896 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e895
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e895
            | exact resolve b8e895 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e895
          have b8e897 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ x) (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b8e13 (σ x) (σ y) X0
               have i₂ := b8e896
               grind)
            | exact superpose b8e896 b8e13
            | exact resolve b8e13 b8e896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e901 : ∀ X0 : G, (M.op (σ x) (σ (k x y))) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e38 X0 (σ y) (σ x)
               have i₂ := b8e896
               grind)
            | exact superpose b8e896 b8e38
            | exact resolve b8e38 b8e896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38
          have b8e1071 : ∀ X0 X1 X3 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (τ (M.op X3 X3)) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e614 X3 x X1
               have i₂ := b8e614 X0 x X1
               grind)
            | exact superpose b8e614 b8e614
            | exact resolve b8e614 b8e614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1586 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e75 x y
               grind)
            | exact superpose b8e75 b8e20
            | (have j1 := b8e75 x y
               grind)
            | exact resolve b8e20 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e1643 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1586
               have r₂ := b8e23
               grind)
            | exact resolve b8e1586 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1586
          have b8e2769 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X1) = (M.op (τ (τ (M.op X0 X0))) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e802 (τ X0) X2 X1
               have i₂ := b8e250 X0
               grind)
            | exact superpose b8e250 b8e802
            | exact resolve b8e802 b8e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e802
          have b8e3233 : ∀ X0 X1 X2 : G, (M.op (τ (τ (M.op X0 X0))) X2) = (M.op (τ (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1071 X1 X2 (τ X0)
               have i₂ := b8e250 X0
               grind)
            | exact superpose b8e250 b8e1071
            | exact resolve b8e1071 b8e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e250 b8e1071
          have b8e4373 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ x) (σ (M.op y x))) ∨ y = (M.op x x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e897 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e897
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e897 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e897
          have b8e4430 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ x) (σ (M.op y x))) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e4373 X0
               grind)
            | (have r₁ := b8e4373 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e4373 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4373
          have b8e4466 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ x) (σ (M.op y x))) := by
            intro X0
            first
            | (have j0 := b8e4430 X0
               grind)
            | (have r₁ := b8e4430 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e4430 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4430
          have b8e4550 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) (σ (M.op y x))) ∨ y = (M.op x x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e901 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e901
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e901 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e901
          have b8e4754 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) (σ (M.op y x))) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e4550 X0
               grind)
            | (have r₁ := b8e4550 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e4550 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4550
          have b8e4758 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) (σ (M.op y x))) := by
            intro X0
            first
            | (have j0 := b8e4754 X0
               grind)
            | (have r₁ := b8e4754 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e4754 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4754
          have b8e8631 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op (M.op X3 (M.op X1 X3)) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 (M.op X3 (M.op X1 X3)) X1
               have i₂ := b8e134 X3 X1 X0 X1
               grind)
            | (have i₁ := b8e13 X0 (M.op X3 (M.op X2 X2)) X2
               have i₂ := b8e134 X0 X1 (M.op X2 X2) X3
               grind)
            | exact superpose b8e134 b8e13
            | exact resolve b8e13 b8e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e14365 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (τ (τ (M.op X0 X0))) (M.op (σ X1) (σ (M.op X2 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e140 X1 (σ (M.op X2 X2))
               have i₂ := b8e2769 X0 (M.op (σ X1) (σ (M.op X2 X2))) X2
               grind)
            | exact superpose b8e2769 b8e140
            | exact resolve b8e140 b8e2769
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e30758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1643
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1643
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e1643
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1643
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1643 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1643
          have b8e30760 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b8e30758
          have b8e30764 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b8e30760
               have r₂ := b8e21
               grind)
            | exact resolve b8e30760 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30760
          have b8e30788 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e30764
               grind)
            | exact superpose b8e30764 b8e14
            | exact resolve b8e14 b8e30764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30764
          have b8e30830 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e30788
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e30788
            | exact resolve b8e30788 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30788
          have b8e30831 : x = (M.op y y) := by grind
          clear b8e30830
          have b8e31376 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 y
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e13
            | exact resolve b8e13 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31379 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) x) = (M.op X1 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 X2 X1 y X0
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e34
            | exact resolve b8e34 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e31403 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x (M.op X2 X2)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e118 y X2 X0 X1
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e118
            | exact resolve b8e118 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31404 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X2) x) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e118 X2 y X0 X1
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e118
            | exact resolve b8e118 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e31409 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e140 y X0
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e140
            | exact resolve b8e140 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31416 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X1) (M.op (σ x) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e202 y X0 X1 X2
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e202
            | exact resolve b8e202 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31427 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e301 X0 X1 X2 y
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e301
            | exact resolve b8e301 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e301
          have b8e31434 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (τ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e614 y X0 X1
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e614
            | exact resolve b8e614 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31435 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (τ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e622 y X0 X1
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e622
            | exact resolve b8e622 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e622
          have b8e31436 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e656 X0 y
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e656
            | exact resolve b8e656 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31450 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (τ (τ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e2769 y X1 X0
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e2769
            | exact resolve b8e2769 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31451 : ∀ X0 X1 : G, (M.op (τ (M.op X1 X1)) X0) = (M.op (τ (τ x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e3233 y X1 X0
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e3233
            | exact resolve b8e3233 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3233
          have b8e31465 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op y (M.op y x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e139 y y X0 X1
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e139
            | exact resolve b8e139 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e31471 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op y (M.op y x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e272 X0 X1 y y
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e272
            | exact resolve b8e272 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e31473 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op y x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e325 y y X0 X1
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e325
            | exact resolve b8e325 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e325
          have b8e31485 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (τ x) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e31427 X0 X1 x
               have i₂ := b8e31435 x x
               grind)
            | exact superpose b8e31435 b8e31427
            | exact resolve b8e31427 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31427
          have b8e31496 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op (σ x) X2)) = (M.op (τ x) X1) := by
            intro X1 X2
            first
            | (have i₁ := b8e31416 x X1 X2
               have i₂ := b8e31435 x X1
               grind)
            | exact superpose b8e31435 b8e31416
            | exact resolve b8e31416 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31416
          have b8e31503 : (M.op (σ y) (σ x)) = (M.op (τ x) (σ y)) := by
            first
            | (have i₁ := b8e31409 x
               have i₂ := b8e31434 x (σ y)
               grind)
            | exact superpose b8e31434 b8e31409
            | exact resolve b8e31409 b8e31434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31409
          have b8e31508 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (τ x) x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e31404 X0 X1 x
               have i₂ := b8e31435 x x
               grind)
            | exact superpose b8e31435 b8e31404
            | exact resolve b8e31404 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31404
          have b8e31509 : ∀ X1 X2 : G, (M.op (M.op x (M.op X2 X2)) X1) = (M.op (τ x) X1) := by
            intro X1 X2
            first
            | (have i₁ := b8e31403 x X1 X2
               have i₂ := b8e31434 x X1
               grind)
            | exact superpose b8e31434 b8e31403
            | exact resolve b8e31403 b8e31434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31403
          have b8e31527 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op y (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b8e31379 X0 x x
               have i₂ := b8e31471 x x
               grind)
            | exact superpose b8e31471 b8e31379
            | exact resolve b8e31379 b8e31471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31379
          have b8e31534 : ∀ X1 : G, (M.op (τ x) x) = (M.op (τ x) (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b8e31485 x X1
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e31485
            | exact resolve b8e31485 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31485
          have b8e31545 : (σ (k x y)) = (M.op (τ x) (σ y)) := by
            first
            | (have i₁ := b8e31503
               have i₂ := b8e896
               grind)
            | exact superpose b8e896 b8e31503
            | exact resolve b8e31503 b8e896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e896 b8e31503
          have b8e31549 : ∀ X1 : G, (M.op (τ x) X1) = (M.op (M.op (τ x) x) X1) := by
            intro X1
            first
            | (have i₁ := b8e31508 x X1
               have i₂ := b8e31434 x X1
               grind)
            | exact superpose b8e31434 b8e31508
            | exact resolve b8e31508 b8e31434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31508
          have b8e31560 : (M.op y (M.op y x)) = (M.op (τ x) x) := by
            first
            | (have i₁ := b8e31527 x
               have i₂ := b8e31435 x x
               grind)
            | exact superpose b8e31435 b8e31527
            | exact resolve b8e31527 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31527
          have b8e31717 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op (σ X1) (M.op (σ X1) (σ (M.op X1 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e292 X1 X0 y
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e292
            | exact resolve b8e292 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31950 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (M.op (M.op X3 X3) X2) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e176 X1 X2 (M.op X3 X3) x
               have i₂ := b8e292 X0 x X3
               grind)
            | exact superpose b8e292 b8e176
            | exact resolve b8e176 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176
          have b8e32065 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X2) = (M.op (M.op X3 X2) (M.op X4 (M.op X3 X4))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b8e153 X4 X3 X2 (M.op x x)
               have i₂ := b8e292 X0 x x
               grind)
            | exact superpose b8e292 b8e153
            | exact resolve b8e153 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153
          have b8e32179 : ∀ X0 X1 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (M.op X0 X0) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e4758 (M.op (σ y) (σ (M.op y y)))
               have i₂ := b8e292 y X0 X1
               grind)
            | exact superpose b8e292 b8e4758
            | exact resolve b8e4758 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32184 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op (σ (M.op X4 X4)) (σ (M.op (M.op X4 X4) (M.op X4 X4)))) X3) (M.op (M.op X0 X0) (M.op X1 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e202 X4 X2 X3 (M.op (σ (M.op X4 X4)) (σ (M.op (M.op X4 X4) (M.op X4 X4))))
               have i₂ := b8e292 (M.op X4 X4) X0 X1
               grind)
            | exact superpose b8e292 b8e202
            | exact resolve b8e202 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e202
          have b8e32191 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (τ (τ (M.op X3 X3))) (M.op (σ (M.op X2 X2)) (σ (M.op (M.op X2 X2) (M.op X2 X2))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e2769 X3 (M.op (σ (M.op X2 X2)) (σ (M.op (M.op X2 X2) (M.op X2 X2)))) X2
               have i₂ := b8e292 (M.op X2 X2) X0 X1
               grind)
            | exact superpose b8e292 b8e2769
            | exact resolve b8e2769 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2769
          have b8e32198 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ (M.op X2 X2))) = (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e140 X2 (M.op (σ X2) (σ (M.op X2 X2)))
               have i₂ := b8e292 X2 X0 X1
               grind)
            | exact superpose b8e292 b8e140
            | exact resolve b8e140 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32227 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op X3 (M.op X4 (M.op X3 X4))) (σ X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e319 X3 X4 (M.op (σ X2) (σ (M.op X2 X2))) (σ X2)
               have i₂ := b8e292 X2 X0 X1
               grind)
            | exact superpose b8e292 b8e319
            | exact resolve b8e319 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319
          have b8e32231 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (τ (M.op X3 X3)) (σ X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e614 X3 (M.op (σ X2) (σ (M.op X2 X2))) (σ X2)
               have i₂ := b8e292 X2 X0 X1
               grind)
            | exact superpose b8e292 b8e614
            | exact resolve b8e614 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e614
          have b8e32239 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (σ X3) X2)) = (M.op X4 (M.op (M.op (M.op (σ X3) (σ (M.op X3 X3))) (M.op (M.op X0 X0) (M.op X1 X1))) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e8631 X2 (σ X3) X4 (M.op (σ X3) (σ (M.op X3 X3)))
               have i₂ := b8e292 X3 X0 X1
               grind)
            | exact superpose b8e292 b8e8631
            | exact resolve b8e8631 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8631
          have b8e32240 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ X3) X2)) = (M.op (τ x) (M.op (M.op (σ X3) (σ (M.op X3 X3))) (M.op (M.op X0 X0) (M.op X1 X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32239 X0 X1 X2 X3 x
               have i₂ := b8e31434 x (M.op (M.op (σ X3) (σ (M.op X3 X3))) (M.op (M.op X0 X0) (M.op X1 X1)))
               grind)
            | exact superpose b8e31434 b8e32239
            | exact resolve b8e32239 b8e31434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32239
          have b8e32247 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (τ (τ x)) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32231 X0 X1 X2 x
               have i₂ := b8e31451 (σ X2) x
               grind)
            | exact superpose b8e31451 b8e32231
            | exact resolve b8e32231 b8e31451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31451 b8e32231
          have b8e32250 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op y (M.op y x)) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32227 X0 X1 X2 x x
               have i₂ := b8e31471 x x
               grind)
            | exact superpose b8e31471 b8e32227
            | exact resolve b8e32227 b8e31471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31471 b8e32227
          have b8e32275 : ∀ X1 X2 : G, (M.op (σ X2) (σ (M.op X2 X2))) = (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (τ x) (M.op X1 X1))) := by
            intro X1 X2
            first
            | (have i₁ := b8e32198 x X1 X2
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e32198
            | exact resolve b8e32198 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32198
          have b8e32279 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (σ (M.op X2 X2)) (σ (M.op (M.op X2 X2) (M.op X2 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32191 X0 X1 X2 x
               have i₂ := b8e14365 x (M.op X2 X2) (M.op X2 X2)
               grind)
            | exact superpose b8e14365 b8e32191
            | exact resolve b8e32191 b8e14365
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14365 b8e32191
          have b8e32286 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op (σ (M.op X4 X4)) (σ (M.op (M.op X4 X4) (M.op X4 X4)))) X3) (M.op (τ x) (M.op X1 X1))) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b8e32184 x X1 X2 X3 X4
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e32184
            | exact resolve b8e32184 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32184
          have b8e32289 : ∀ X1 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (τ x) (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b8e32179 x X1
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e32179
            | exact resolve b8e32179 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32179
          have b8e32394 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X2) = (M.op (M.op X3 X2) (M.op (τ x) X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e32065 X0 X2 X3 x
               have i₂ := b8e31434 x X3
               grind)
            | exact superpose b8e31434 b8e32065
            | exact resolve b8e32065 b8e31434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32065
          have b8e32430 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (M.op (M.op X3 X3) X2) (M.op (σ X0) (M.op (σ x) (σ X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e31950 X0 X1 X2 X3
               have i₂ := b8e31436 X0
               grind)
            | exact superpose b8e31436 b8e31950
            | exact resolve b8e31950 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31950
          have b8e32550 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op (σ X1) (M.op (σ x) (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e31717 X0 X1
               have i₂ := b8e31436 X1
               grind)
            | exact superpose b8e31436 b8e31717
            | exact resolve b8e31717 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31717
          have b8e32675 : ∀ X1 X2 X3 : G, (M.op X2 (M.op (σ X3) X2)) = (M.op (τ x) (M.op (M.op (σ X3) (σ (M.op X3 X3))) (M.op (τ x) (M.op X1 X1)))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e32240 x X1 X2 X3
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e32240
            | exact resolve b8e32240 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32240
          have b8e32682 : ∀ X1 X2 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (τ x) (M.op X1 X1))) = (M.op (τ (τ x)) (σ X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e32247 x X1 X2
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e32247
            | exact resolve b8e32247 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32247
          have b8e32685 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (τ x) x) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32250 X0 X1 X2
               have i₂ := b8e31560
               grind)
            | exact superpose b8e31560 b8e32250
            | exact resolve b8e32250 b8e31560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32250
          have b8e32710 : ∀ X2 : G, (M.op (σ X2) (σ (M.op X2 X2))) = (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e32275 x X2
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e32275
            | exact resolve b8e32275 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32275
          have b8e32714 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (σ x) (σ (M.op X2 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32279 X0 X1 X2
               have i₂ := b8e31436 (M.op X2 X2)
               grind)
            | exact superpose b8e31436 b8e32279
            | exact resolve b8e32279 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32279
          have b8e32721 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op (σ (M.op X4 X4)) (σ (M.op (M.op X4 X4) (M.op X4 X4)))) X3) (M.op (τ x) x)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b8e32286 x X2 X3 X4
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e32286
            | exact resolve b8e32286 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32286
          have b8e32724 : (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (τ x) x)) := by
            first
            | (have i₁ := b8e32289 x
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e32289
            | exact resolve b8e32289 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32289
          have b8e32829 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (M.op (σ x) (σ X0))) X2) = (M.op (M.op X3 X2) (M.op (τ x) X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e32394 X0 X2 X3
               have i₂ := b8e31436 X0
               grind)
            | exact superpose b8e31436 b8e32394
            | exact resolve b8e32394 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32394
          have b8e32865 : ∀ X1 X2 X3 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (M.op (M.op X3 X3) X2) (M.op (σ x) (σ (M.op x x)))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e32430 x X1 X2 X3
               have i₂ := b8e140 x (σ x)
               grind)
            | exact superpose b8e140 b8e32430
            | exact resolve b8e32430 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32430
          have b8e32981 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (σ x) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b8e32550 X0 x
               have i₂ := b8e140 x (σ x)
               grind)
            | exact superpose b8e140 b8e32550
            | exact resolve b8e32550 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32550
          have b8e33106 : ∀ X2 X3 : G, (M.op X2 (M.op (σ X3) X2)) = (M.op (τ x) (M.op (M.op (σ X3) (σ (M.op X3 X3))) (M.op (τ x) x))) := by
            intro X2 X3
            first
            | (have i₁ := b8e32675 x X2 X3
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e32675
            | exact resolve b8e32675 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32675
          have b8e33113 : ∀ X2 : G, (M.op (τ (τ x)) (σ X2)) = (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e32682 x X2
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e32682
            | exact resolve b8e32682 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32682
          have b8e33116 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (τ x) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32685 X0 X1 X2
               have i₂ := b8e31549 (σ X2)
               grind)
            | exact superpose b8e31549 b8e32685
            | exact resolve b8e32685 b8e31549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32685
          have b8e33141 : ∀ X2 : G, (M.op (σ x) (σ X2)) = (M.op (M.op (σ x) (σ X2)) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e32710 x
               have i₂ := b8e31436 x
               grind)
            | exact superpose b8e31436 b8e32710
            | exact resolve b8e32710 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32710
          have b8e33145 : ∀ X1 X2 : G, (M.op (τ x) (M.op X1 X1)) = (M.op (σ x) (σ (M.op X2 X2))) := by
            intro X1 X2
            first
            | (have i₁ := b8e32714 x X1 X2
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e32714
            | exact resolve b8e32714 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32714
          have b8e33152 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op (σ x) (σ (M.op X4 X4))) X3) (M.op (τ x) x)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b8e32721 X2 X3 X4
               have i₂ := b8e31436 (M.op X4 X4)
               grind)
            | exact superpose b8e31436 b8e32721
            | exact resolve b8e32721 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32721
          have b8e33155 : (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ x) (σ y)) (M.op (τ x) x)) := by
            first
            | (have i₁ := b8e32724
               have i₂ := b8e31436 y
               grind)
            | exact superpose b8e31436 b8e32724
            | exact resolve b8e32724 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32724
          have b8e33260 : ∀ X2 X3 : G, (M.op (M.op (σ x) (σ (M.op x x))) X2) = (M.op (M.op X3 X2) (M.op (τ x) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e32829 x X2 X3
               have i₂ := b8e140 x (σ x)
               grind)
            | exact superpose b8e140 b8e32829
            | exact resolve b8e32829 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140 b8e32829
          have b8e33296 : ∀ X1 X2 X3 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (M.op (M.op X3 X3) X2) (M.op (σ x) (σ x))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e32865 X1 X2 X3
               have i₂ := b8e31436 x
               grind)
            | exact superpose b8e31436 b8e32865
            | exact resolve b8e32865 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32865
          have b8e33406 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 X0) x) := by
            intro X0
            first
            | (have i₁ := b8e32981 X0
               have i₂ := b8e31436 x
               grind)
            | exact superpose b8e31436 b8e32981
            | exact resolve b8e32981 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32981
          have b8e33531 : ∀ X2 X3 : G, (M.op X2 (M.op (σ X3) X2)) = (M.op (τ x) (M.op (M.op (σ x) (σ X3)) (M.op (τ x) x))) := by
            intro X2 X3
            first
            | (have i₁ := b8e33106 X2 X3
               have i₂ := b8e31436 X3
               grind)
            | exact superpose b8e31436 b8e33106
            | exact resolve b8e33106 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33106
          have b8e33534 : ∀ X2 : G, (M.op (τ (τ x)) (σ X2)) = (M.op (M.op (σ x) (σ X2)) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e33113 X2
               have i₂ := b8e31436 X2
               grind)
            | exact superpose b8e31436 b8e33113
            | exact resolve b8e33113 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33113
          have b8e33537 : ∀ X1 X2 : G, (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (τ x) (M.op X1 X1))) = (M.op (τ x) (σ X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e33116 x X1 X2
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e33116
            | exact resolve b8e33116 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33116
          have b8e33564 : ∀ X2 : G, (M.op (τ x) x) = (M.op (σ x) (σ (M.op X2 X2))) := by
            intro X2
            first
            | (have i₁ := b8e33145 x X2
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e33145
            | exact resolve b8e33145 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33145
          have b8e33571 : ∀ X3 X4 : G, (M.op (τ x) X3) = (M.op (M.op (M.op (σ x) (σ (M.op X4 X4))) X3) (M.op (τ x) x)) := by
            intro X3 X4
            first
            | (have i₁ := b8e33152 x X3 X4
               have i₂ := b8e31435 x X3
               grind)
            | exact superpose b8e31435 b8e33152
            | exact resolve b8e33152 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33152
          have b8e33574 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op y x))) := by
            first
            | (have i₁ := b8e33155
               have i₂ := b8e33141 y
               grind)
            | exact superpose b8e33141 b8e33155
            | exact resolve b8e33155 b8e33141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33155
          have b8e33633 : ∀ X2 X3 : G, (M.op (M.op X3 X2) (M.op (τ x) X3)) = (M.op (M.op (σ x) (σ x)) X2) := by
            intro X2 X3
            first
            | (have i₁ := b8e33260 X2 X3
               have i₂ := b8e31436 x
               grind)
            | exact superpose b8e31436 b8e33260
            | exact resolve b8e33260 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33260
          have b8e33652 : ∀ X1 X2 X3 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (M.op (M.op X3 X3) X2) (σ (M.op x x))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e33296 X1 X2 X3
               have i₂ := b8e31 x
               grind)
            | exact superpose b8e31 b8e33296
            | exact resolve b8e33296 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33296
          have b8e33740 : (M.op (σ x) (σ x)) = (M.op (τ x) x) := by
            first
            | (have i₁ := b8e33406 x
               have i₂ := b8e31435 x x
               grind)
            | exact superpose b8e31435 b8e33406
            | exact resolve b8e33406 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33406
          have b8e33864 : ∀ X2 X3 : G, (M.op X2 (M.op (σ X3) X2)) = (M.op (τ x) (M.op (σ x) (σ X3))) := by
            intro X2 X3
            first
            | (have i₁ := b8e33531 X2 X3
               have i₂ := b8e33141 X3
               grind)
            | exact superpose b8e33141 b8e33531
            | exact resolve b8e33531 b8e33141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33531
          have b8e33867 : ∀ X2 : G, (M.op (σ x) (σ X2)) = (M.op (τ (τ x)) (σ X2)) := by
            intro X2
            first
            | (have i₁ := b8e33534 X2
               have i₂ := b8e33141 X2
               grind)
            | exact superpose b8e33141 b8e33534
            | exact resolve b8e33534 b8e33141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33534
          have b8e33870 : ∀ X2 : G, (M.op (τ x) (σ X2)) = (M.op (M.op (σ X2) (σ (M.op X2 X2))) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e33537 x X2
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e33537
            | exact resolve b8e33537 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33537
          have b8e33895 : ∀ X3 : G, (M.op (τ x) X3) = (M.op (M.op (M.op (τ x) x) X3) (M.op (τ x) x)) := by
            intro X3
            first
            | (have i₁ := b8e33571 X3 x
               have i₂ := b8e33564 x
               grind)
            | exact superpose b8e33564 b8e33571
            | exact resolve b8e33571 b8e33564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33564 b8e33571
          have b8e33954 : ∀ X2 X3 : G, (M.op (M.op y (M.op y x)) X2) = (M.op (M.op X3 X2) (M.op (τ x) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e33633 X2 X3
               have i₂ := b8e31473 (σ x) X2
               grind)
            | exact superpose b8e31473 b8e33633
            | exact resolve b8e33633 b8e31473
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31473 b8e33633
          have b8e33971 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (M.op (τ x) X2) (σ (M.op x x))) := by
            intro X1 X2
            first
            | (have i₁ := b8e33652 X1 X2 x
               have i₂ := b8e31435 x X2
               grind)
            | exact superpose b8e31435 b8e33652
            | exact resolve b8e33652 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33652
          have b8e34040 : (σ (M.op x x)) = (M.op (τ x) x) := by
            first
            | (have i₁ := b8e33740
               have i₂ := b8e31 x
               grind)
            | exact superpose b8e31 b8e33740
            | exact resolve b8e33740 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e33740
          have b8e34157 : ∀ X3 : G, (M.op (τ x) (σ X3)) = (M.op (τ x) (M.op (σ x) (σ X3))) := by
            intro X3
            first
            | (have i₁ := b8e33864 x X3
               have i₂ := b8e31434 x (σ X3)
               grind)
            | exact superpose b8e31434 b8e33864
            | exact resolve b8e33864 b8e31434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31434 b8e33864
          have b8e34160 : ∀ X2 : G, (M.op (τ x) (σ X2)) = (M.op (M.op (σ x) (σ X2)) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e33870 X2
               have i₂ := b8e31436 X2
               grind)
            | exact superpose b8e31436 b8e33870
            | exact resolve b8e33870 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33870
          have b8e34178 : ∀ X3 : G, (M.op (τ x) X3) = (M.op (M.op (τ x) X3) (M.op (τ x) x)) := by
            intro X3
            first
            | (have i₁ := b8e33895 X3
               have i₂ := b8e31549 X3
               grind)
            | exact superpose b8e31549 b8e33895
            | exact resolve b8e33895 b8e31549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33895
          have b8e34236 : ∀ X2 X3 : G, (M.op (M.op X3 X2) (M.op (τ x) X3)) = (M.op (M.op (τ x) x) X2) := by
            intro X2 X3
            first
            | (have i₁ := b8e33954 X2 X3
               have i₂ := b8e31560
               grind)
            | exact superpose b8e31560 b8e33954
            | exact resolve b8e33954 b8e31560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33954
          have b8e34252 : ∀ X2 : G, (M.op (M.op (τ x) X2) (σ (M.op x x))) = (M.op (τ (τ x)) X2) := by
            intro X2
            first
            | (have i₁ := b8e33971 x X2
               have i₂ := b8e31450 x X2
               grind)
            | exact superpose b8e31450 b8e33971
            | exact resolve b8e33971 b8e31450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33971
          have b8e34430 : ∀ X2 : G, (M.op (σ x) (σ X2)) = (M.op (τ x) (σ X2)) := by
            intro X2
            first
            | (have i₁ := b8e34160 X2
               have i₂ := b8e33141 X2
               grind)
            | exact superpose b8e33141 b8e34160
            | exact resolve b8e34160 b8e33141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33141 b8e34160
          have b8e34498 : ∀ X2 X3 : G, (M.op (τ x) X2) = (M.op (M.op X3 X2) (M.op (τ x) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e34236 X2 X3
               have i₂ := b8e31549 X2
               grind)
            | exact superpose b8e31549 b8e34236
            | exact resolve b8e34236 b8e31549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34236
          have b8e34511 : ∀ X2 : G, (M.op (τ (τ x)) X2) = (M.op (M.op (τ x) X2) (M.op (τ x) x)) := by
            intro X2
            first
            | (have i₁ := b8e34252 X2
               have i₂ := b8e34040
               grind)
            | exact superpose b8e34040 b8e34252
            | exact resolve b8e34252 b8e34040
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34040 b8e34252
          have b8e34707 : ∀ X2 : G, (M.op (τ x) X2) = (M.op (τ (τ x)) X2) := by
            intro X2
            first
            | (have i₁ := b8e34511 X2
               have i₂ := b8e34178 X2
               grind)
            | exact superpose b8e34178 b8e34511
            | exact resolve b8e34511 b8e34178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34178 b8e34511
          have b8e44512 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ (M.op y x)))) := by
            intro X0
            first
            | (have i₁ := b8e31376 (M.op (σ y) X0) X0
               have i₂ := b8e4758 X0
               grind)
            | exact superpose b8e4758 b8e31376
            | exact resolve b8e31376 b8e4758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44576 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (M.op (σ (M.op X0 X0)) (σ X1))) = (M.op x (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e31376 (σ (M.op X1 X1)) (σ X1)
               have i₂ := b8e656 X1 X0
               grind)
            | exact superpose b8e656 b8e31376
            | exact resolve b8e31376 b8e656
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e656
          have b8e44621 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b8e31376 y y
               have i₂ := b8e30831
               grind)
            | exact superpose b8e30831 b8e31376
            | exact resolve b8e31376 b8e30831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30831
          have b8e44788 : (M.op (σ x) (σ (M.op y x))) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e4758 x
               have i₂ := b8e31376 x (σ y)
               grind)
            | exact superpose b8e31376 b8e4758
            | exact resolve b8e4758 b8e31376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4758
          have b8e44853 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e35 X1 (M.op X0 (M.op X2 X2)) X2
               have i₂ := b8e31376 (M.op X2 X2) X0
               grind)
            | exact superpose b8e31376 b8e35
            | exact resolve b8e35 b8e31376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35 b8e31376
          have b8e45008 : ∀ X0 X2 : G, (M.op x X0) = (M.op (τ x) (M.op X0 (M.op X2 X2))) := by
            intro X0 X2
            first
            | (have i₁ := b8e44853 X0 x X2
               have i₂ := b8e31435 x (M.op X0 (M.op X2 X2))
               grind)
            | exact superpose b8e31435 b8e44853
            | exact resolve b8e44853 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44853
          have b8e45229 : ∀ X0 X1 : G, (M.op x (σ X1)) = (M.op (τ (τ x)) (M.op (σ (M.op X0 X0)) (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e44576 X0 X1
               have i₂ := b8e31450 X1 (M.op (σ (M.op X0 X0)) (σ X1))
               grind)
            | exact superpose b8e31450 b8e44576
            | exact resolve b8e44576 b8e31450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44576
          have b8e45290 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b8e44512 X0
               have i₂ := b8e33574
               grind)
            | exact superpose b8e33574 b8e44512
            | exact resolve b8e44512 b8e33574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33574 b8e44512
          have b8e45541 : ∀ X0 X1 : G, (M.op x (σ X1)) = (M.op (τ x) (M.op (σ (M.op X0 X0)) (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e45229 X0 X1
               have i₂ := b8e34707 (M.op (σ (M.op X0 X0)) (σ X1))
               grind)
            | exact superpose b8e34707 b8e45229
            | exact resolve b8e45229 b8e34707
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34707 b8e45229
          have b8e45599 : ∀ X0 : G, (M.op x X0) = (M.op (τ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e45290 X0
               have i₂ := b8e31496 X0 (σ y)
               grind)
            | exact superpose b8e31496 b8e45290
            | exact resolve b8e45290 b8e31496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31496 b8e45290
          have b8e45773 : ∀ X1 : G, (M.op x (σ X1)) = (M.op (τ x) (M.op (τ (τ x)) (σ X1))) := by
            intro X1
            first
            | (have i₁ := b8e45541 x X1
               have i₂ := b8e31450 x (σ X1)
               grind)
            | exact superpose b8e31450 b8e45541
            | exact resolve b8e45541 b8e31450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31450 b8e45541
          have b8e45932 : ∀ X1 : G, (M.op x (σ X1)) = (M.op x (M.op (τ (τ x)) (σ X1))) := by
            intro X1
            first
            | (have i₁ := b8e45773 X1
               have i₂ := b8e45599 (M.op (τ (τ x)) (σ X1))
               grind)
            | exact superpose b8e45599 b8e45773
            | exact resolve b8e45773 b8e45599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45773
          have b8e46035 : ∀ X1 : G, (M.op x (σ X1)) = (M.op x (M.op (σ x) (σ X1))) := by
            intro X1
            first
            | (have i₁ := b8e45932 X1
               have i₂ := b8e33867 X1
               grind)
            | exact superpose b8e33867 b8e45932
            | exact resolve b8e45932 b8e33867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33867 b8e45932
          have b8e47098 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op (M.op X3 X3) X0)) (σ y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e4466 (M.op (M.op X1 X1) (M.op X2 X2))
               have i₂ := b8e174 X1 X2 (M.op (M.op X1 X1) (M.op X2 X2)) X0 X3
               grind)
            | (have i₁ := b8e4466 (M.op (M.op x x) (M.op x x))
               have i₂ := b8e174 X0 X1 (M.op x x) (M.op x x) x
               grind)
            | exact superpose b8e174 b8e4466
            | exact resolve b8e4466 b8e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174 b8e4466
          have b8e47675 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 X2))) (M.op (τ x) X0)) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e47098 X0 X1 X2 x
               have i₂ := b8e31435 x X0
               grind)
            | exact superpose b8e31435 b8e47098
            | exact resolve b8e47098 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47098
          have b8e48478 : ∀ X1 X2 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (τ x) (M.op (M.op X1 X1) (M.op X2 X2))) (σ y)) := by
            intro X1 X2
            first
            | (have i₁ := b8e47675 x X1 X2
               have i₂ := b8e34498 (M.op (M.op X1 X1) (M.op X2 X2)) x
               grind)
            | exact superpose b8e34498 b8e47675
            | exact resolve b8e47675 b8e34498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34498 b8e47675
          have b8e49268 : ∀ X1 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op x (M.op X1 X1)) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e48478 X1 x
               have i₂ := b8e45008 (M.op X1 X1) x
               grind)
            | exact superpose b8e45008 b8e48478
            | exact resolve b8e48478 b8e45008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45008 b8e48478
          have b8e50047 : (M.op (σ x) (σ (M.op y x))) = (M.op (τ x) (σ y)) := by
            first
            | (have i₁ := b8e49268 x
               have i₂ := b8e31509 (σ y) x
               grind)
            | exact superpose b8e31509 b8e49268
            | exact resolve b8e49268 b8e31509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31509 b8e49268
          have b8e50793 : (σ (k x y)) = (M.op (σ x) (σ (M.op y x))) := by
            first
            | (have i₁ := b8e50047
               have i₂ := b8e31545
               grind)
            | exact superpose b8e31545 b8e50047
            | exact resolve b8e50047 b8e31545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31545 b8e50047
          have b8e51494 : (σ (k x y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e50793
               have i₂ := b8e44788
               grind)
            | exact superpose b8e44788 b8e50793
            | exact resolve b8e50793 b8e44788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44788 b8e50793
          have b8e54606 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X5 X5) (σ X4))) = (M.op (M.op X2 (M.op (M.op X3 X3) X2)) (M.op (σ X4) (σ (M.op X4 X4)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e175 X2 X3 (M.op (σ X4) (σ (M.op X4 X4))) (σ X4) X5
               have i₂ := b8e292 X4 X0 X1
               grind)
            | exact superpose b8e292 b8e175
            | exact resolve b8e175 b8e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175 b8e292
          have b8e55889 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X5 X5) (σ X4))) = (M.op (M.op X2 (M.op (M.op X3 X3) X2)) (M.op (σ x) (σ X4))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e54606 X0 X1 X2 X3 X4 X5
               have i₂ := b8e31436 X4
               grind)
            | exact superpose b8e31436 b8e54606
            | exact resolve b8e54606 b8e31436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31436 b8e54606
          have b8e56782 : ∀ X0 X1 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X5 X5) (σ X4))) = (M.op (M.op y (M.op y x)) (M.op (σ x) (σ X4))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e55889 X0 X1 x x X4 X5
               have i₂ := b8e31465 x x
               grind)
            | exact superpose b8e31465 b8e55889
            | exact resolve b8e55889 b8e31465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31465 b8e55889
          have b8e57669 : ∀ X0 X1 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X5 X5) (σ X4))) = (M.op (M.op (τ x) x) (M.op (σ x) (σ X4))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e56782 X0 X1 X4 X5
               have i₂ := b8e31560
               grind)
            | exact superpose b8e31560 b8e56782
            | exact resolve b8e56782 b8e31560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31560 b8e56782
          have b8e58540 : ∀ X0 X1 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X5 X5) (σ X4))) = (M.op (τ x) (M.op (σ x) (σ X4))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e57669 X0 X1 X4 X5
               have i₂ := b8e31549 (M.op (σ x) (σ X4))
               grind)
            | exact superpose b8e31549 b8e57669
            | exact resolve b8e57669 b8e31549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57669
          have b8e59374 : ∀ X0 X1 X4 X5 : G, (M.op (τ x) (σ X4)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X5 X5) (σ X4))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e58540 X0 X1 X4 X5
               have i₂ := b8e34157 X4
               grind)
            | exact superpose b8e34157 b8e58540
            | exact resolve b8e58540 b8e34157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34157 b8e58540
          have b8e60180 : ∀ X0 X1 X4 : G, (M.op (τ x) (σ X4)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (τ x) (σ X4))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e59374 X0 X1 X4 x
               have i₂ := b8e31435 x (σ X4)
               grind)
            | exact superpose b8e31435 b8e59374
            | exact resolve b8e59374 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59374
          have b8e60882 : ∀ X0 X1 X4 : G, (M.op (σ x) (σ X4)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (σ x) (σ X4))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e60180 X0 X1 x
               have i₂ := b8e34430 x
               grind)
            | exact superpose b8e34430 b8e60180
            | exact resolve b8e60180 b8e34430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34430 b8e60180
          have b8e61498 : ∀ X1 X4 : G, (M.op (σ x) (σ X4)) = (M.op (M.op (τ x) (M.op X1 X1)) (M.op (σ x) (σ X4))) := by
            intro X1 X4
            first
            | (have i₁ := b8e60882 x X1 X4
               have i₂ := b8e31435 x (M.op X1 X1)
               grind)
            | exact superpose b8e31435 b8e60882
            | exact resolve b8e60882 b8e31435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31435 b8e60882
          have b8e61993 : ∀ X4 : G, (M.op (σ x) (σ X4)) = (M.op (M.op (τ x) x) (M.op (σ x) (σ X4))) := by
            intro X4
            first
            | (have i₁ := b8e61498 x X4
               have i₂ := b8e31534 x
               grind)
            | exact superpose b8e31534 b8e61498
            | exact resolve b8e61498 b8e31534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31534 b8e61498
          have b8e62372 : ∀ X4 : G, (M.op (σ x) (σ X4)) = (M.op (τ x) (M.op (σ x) (σ X4))) := by
            intro X4
            first
            | (have i₁ := b8e61993 X4
               have i₂ := b8e31549 (M.op (σ x) (σ X4))
               grind)
            | exact superpose b8e31549 b8e61993
            | exact resolve b8e61993 b8e31549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31549 b8e61993
          have b8e62651 : ∀ X4 : G, (M.op (σ x) (σ X4)) = (M.op x (M.op (σ x) (σ X4))) := by
            intro X4
            first
            | (have i₁ := b8e62372 X4
               have i₂ := b8e45599 (M.op (σ x) (σ X4))
               grind)
            | exact superpose b8e45599 b8e62372
            | exact resolve b8e62372 b8e45599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45599 b8e62372
          have b8e62855 : ∀ X4 : G, (M.op (σ x) (σ X4)) = (M.op x (σ X4)) := by
            intro X4
            first
            | (have i₁ := b8e62651 X4
               have i₂ := b8e46035 X4
               grind)
            | exact superpose b8e46035 b8e62651
            | exact resolve b8e62651 b8e46035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46035 b8e62651
          have b8e121398 : (σ (M.op y x)) = (M.op x (σ y)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e51494
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e51494
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e51494 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51494
          have b8e121424 : (σ (M.op y x)) = (M.op x (σ y)) ∨ x = y := by
            first
            | (have r₁ := b8e121398
               have r₂ := b8e22
               grind)
            | exact resolve b8e121398 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121398
          have b8e121426 : (σ (M.op y x)) = (M.op x (σ y)) := by
            first
            | (have r₁ := b8e121424
               have r₂ := b8e21
               grind)
            | exact resolve b8e121424 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121424
          have b8e121427 : (σ (M.op x y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e121426
               have i₂ := b8e44621
               grind)
            | exact superpose b8e44621 b8e121426
            | exact resolve b8e121426 b8e44621
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44621 b8e121426
          have b8e135154 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62855 y
               grind)
            | exact superpose b8e62855 b8e20
            | exact resolve b8e20 b8e62855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62855
          have b8e135427 : False := by grind
          exact b8e135427

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation4461 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4461 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e28
      have b0e78 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e83 : False := by grind
      exact b0e83
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : False := by grind
        exact b1e28
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : False := by grind
        exact b2e28
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b4e39 x X1
               have i₂ := b4e40 x X1
               grind)
            | exact superpose b4e40 b4e39
            | exact resolve b4e39 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e69 X0 X1
               have i₂ := b4e31 X1
               grind)
            | exact superpose b4e31 b4e69
            | (have j0 := b4e69 X0 X1
               grind)
            | exact resolve b4e69 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e84 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 (M.op X0 X1) X1
               have i₂ := b4e40 X1 X0
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op y (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e40 X0 (σ y)
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e40
            | exact resolve b4e40 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : (M.op y y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e89 x
               have i₂ := b4e40 x y
               grind)
            | exact superpose b4e40 b4e89
            | exact resolve b4e89 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e89
          have b4e137 : (M.op y (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e43 (σ y)
               have i₂ := b4e31 y
               grind)
            | exact superpose b4e31 b4e43
            | exact resolve b4e43 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e43
          have b4e146 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e137
               have i₂ := b4e100
               grind)
            | exact superpose b4e100 b4e137
            | exact resolve b4e137 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100 b4e137
          have b4e2448 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e81 x y
               grind)
            | exact superpose b4e81 b4e20
            | (have j1 := b4e81 x y
               grind)
            | exact resolve b4e20 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e2500 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e2448
               have r₂ := b4e23
               grind)
            | exact resolve b4e2448 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2448
          have b4e2542 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op y y) := by
            first
            | (have i₁ := b4e2500
               have i₂ := b4e146
               grind)
            | exact superpose b4e146 b4e2500
            | exact resolve b4e2500 b4e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e146 b4e2500
          have b4e8020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e2542
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e2542
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e2542
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e2542
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e2542 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2542
          have b4e8022 : (σ x) = (M.op y y) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b4e8020
          have b4e8027 : (σ x) = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b4e8022
               have r₂ := b4e21
               grind)
            | exact resolve b4e8022 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8022
          have b4e8074 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e84 y y
               have i₂ := b4e8027
               grind)
            | exact superpose b4e8027 b4e84
            | exact resolve b4e84 b4e8027
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8027
          have b4e8080 : (σ x) = (σ y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e8074
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e8074
            | exact resolve b4e8074 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8074
          have b4e8100 : x = (M.op y y) := by
            first
            | (have r₁ := b4e8080
               have r₂ := b4e23
               grind)
            | exact resolve b4e8080 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8080
          have b4e8173 : x = (M.op x x) := by
            first
            | (have i₁ := b4e84 y y
               have i₂ := b4e8100
               grind)
            | exact superpose b4e8100 b4e84
            | exact resolve b4e84 b4e8100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84 b4e8100
          have b4e8876 : x = y := by
            first
            | (have i₁ := b4e22
               have i₂ := b4e8173
               grind)
            | exact superpose b4e8173 b4e22
            | exact resolve b4e22 b4e8173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8173
          have b4e8929 : False := by grind
          exact b4e8929
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e146 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e24
            | exact resolve b5e24 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e157 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e146
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e146
            | exact resolve b5e146 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146
          have b5e158 : False := by grind
          exact b5e158
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : x = y := by
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
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e111 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e24
            | exact resolve b7e24 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e148 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e14
            | exact resolve b7e14 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e149 : y = (M.op x x) := by
            first
            | (have i₁ := b7e148
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e148
            | exact resolve b7e148 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148
          have b7e153 : False := by grind
          exact b7e153
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X1 X2) X2 X3
               have i₂ := b8e13 X2 X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op X2 X2) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e13 x X1 X3
               have i₂ := b8e13 x X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e13 X2 X1 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e27
          have b8e45 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e41 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e41
            | exact resolve b8e41 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e46 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e45
          have b8e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = X0 := by
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
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (M.op (σ x) (σ x))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ x) (σ x)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e65 X0 X1
               have i₂ := b8e31 X1
               grind)
            | exact superpose b8e31 b8e65
            | (have j0 := b8e65 X0 X1
               grind)
            | exact resolve b8e65 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e81 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) (σ X0) X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e100 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (M.op X1 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e35 X1 X2 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e35
            | exact resolve b8e35 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e117 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op X1 X1)
               have i₂ := b8e35 X1 (M.op X1 X1) X0
               grind)
            | (have i₁ := b8e13 X2 X3 (M.op X1 X1)
               have i₂ := b8e35 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b8e35 b8e13
            | exact resolve b8e13 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e139 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X1 (σ X0) (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e38
            | exact resolve b8e38 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e175 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 X1) (M.op (M.op X3 X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e33 X3 X2 X1 (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e33
            | exact resolve b8e33 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e194 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ (M.op X0 X0)) (M.op (M.op X2 X2) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 X2 (σ X0) (σ X0) X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e33
            | exact resolve b8e33 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e201 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op X3 X2) (M.op (σ (M.op X0 X0)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e33 (σ X0) X3 X2 X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e33
            | exact resolve b8e33 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e249 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e46 X0
               grind)
            | exact superpose b8e46 b8e14
            | exact resolve b8e14 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e271 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X4 (M.op X5 (M.op X4 X5))) := by
            intro X0 X1 X4 X5
            first
            | (have i₁ := b8e34 X5 X4 x x
               have i₂ := b8e34 X1 X0 x x
               grind)
            | exact superpose b8e34 b8e34
            | exact resolve b8e34 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e291 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 (σ X0) (σ X0) X2 X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e34
            | exact resolve b8e34 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e300 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e34 x x X1 X0
               have i₂ := b8e34 x x X3 X2
               grind)
            | exact superpose b8e34 b8e34
            | exact resolve b8e34 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e324 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e35 X2 X3 (M.op x x)
               have i₂ := b8e34 X1 X0 x x
               grind)
            | exact superpose b8e34 b8e35
            | exact resolve b8e35 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e612 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (τ X0)
               have i₂ := b8e249 X0
               grind)
            | exact superpose b8e249 b8e13
            | exact resolve b8e13 b8e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e620 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e35 X1 X2 (τ X0)
               have i₂ := b8e249 X0
               grind)
            | exact superpose b8e249 b8e35
            | exact resolve b8e35 b8e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e654 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X1 X1)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 X1 (σ X0) (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e84
            | exact resolve b8e84 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e800 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (σ (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e100 X1 (τ X0) X2
               have i₂ := b8e249 X0
               grind)
            | exact superpose b8e249 b8e100
            | exact resolve b8e100 b8e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e892 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e71 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e893 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e892
               have r₂ := b8e23
               grind)
            | exact resolve b8e892 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e892
          have b8e894 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e893
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e893
            | exact resolve b8e893 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e893
          have b8e899 : ∀ X0 : G, (M.op (σ x) (σ (k x y))) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e38 X0 (σ y) (σ x)
               have i₂ := b8e894
               grind)
            | exact superpose b8e894 b8e38
            | exact resolve b8e38 b8e894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38
          have b8e900 : ∀ X0 : G, (M.op (σ x) (σ (k x y))) = (M.op (σ (M.op X0 X0)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e84 X0 (σ x) (σ y)
               have i₂ := b8e894
               grind)
            | exact superpose b8e894 b8e84
            | exact resolve b8e84 b8e894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e901 : (M.op (σ x) (σ (k x y))) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b8e900 x
               have i₂ := b8e654 y x
               grind)
            | exact superpose b8e654 b8e900
            | exact resolve b8e900 b8e654
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e900
          have b8e1584 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e74 x y
               grind)
            | exact superpose b8e74 b8e20
            | (have j1 := b8e74 x y
               grind)
            | exact resolve b8e20 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e1641 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1584
               have r₂ := b8e23
               grind)
            | exact resolve b8e1584 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1584
          have b8e2759 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) X1) = (M.op (τ (τ (M.op X0 X0))) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e800 (τ X0) X2 X1
               have i₂ := b8e249 X0
               grind)
            | exact superpose b8e249 b8e800
            | exact resolve b8e800 b8e249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e249 b8e800
          have b8e4319 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) (σ (M.op y x))) ∨ y = (M.op x x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e899 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e899
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e899 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4523 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) (σ (M.op y x))) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e4319 X0
               grind)
            | (have r₁ := b8e4319 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e4319 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4319
          have b8e4527 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) (σ (M.op y x))) := by
            intro X0
            first
            | (have j0 := b8e4523 X0
               grind)
            | (have r₁ := b8e4523 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e4523 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4523
          have b8e29616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1641
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1641
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e1641
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1641
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1641 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1641
          have b8e29618 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b8e29616
          have b8e29622 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b8e29618
               have r₂ := b8e21
               grind)
            | exact resolve b8e29618 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29618
          have b8e29646 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e29622
               grind)
            | exact superpose b8e29622 b8e14
            | exact resolve b8e14 b8e29622
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29622
          have b8e29688 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e29646
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e29646
            | exact resolve b8e29646 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29646
          have b8e29689 : x = (M.op y y) := by grind
          clear b8e29688
          have b8e30008 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b8e901
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e901
            | exact resolve b8e901 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e901
          have b8e30009 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 y
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e13
            | exact resolve b8e13 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e30012 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) x) = (M.op X1 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 X2 X1 y X0
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e34
            | exact resolve b8e34 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e30025 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 y X0 X1
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e84
            | exact resolve b8e84 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e30036 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X2) x) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e117 X2 y X0 X1
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e117
            | exact resolve b8e117 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e30057 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X2 X2) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e300 X0 X1 X2 y
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e300
            | exact resolve b8e300 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e300
          have b8e30063 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (τ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e612 y X0 X1
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e612
            | exact resolve b8e612 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e612
          have b8e30064 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (τ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e620 y X0 X1
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e620
            | exact resolve b8e620 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e620
          have b8e30065 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e654 X0 y
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e654
            | exact resolve b8e654 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e654
          have b8e30079 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (τ (τ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e2759 y X1 X0
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e2759
            | exact resolve b8e2759 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2759
          have b8e30097 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op y (M.op y x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e271 X0 X1 y y
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e271
            | exact resolve b8e271 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271
          have b8e30099 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op y x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e324 y y X0 X1
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e324
            | exact resolve b8e324 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e324
          have b8e30108 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (τ x) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e30057 X0 X1 x
               have i₂ := b8e30064 x x
               grind)
            | exact superpose b8e30064 b8e30057
            | exact resolve b8e30057 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30057
          have b8e30129 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (τ x) x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30036 X0 X1 x
               have i₂ := b8e30064 x x
               grind)
            | exact superpose b8e30064 b8e30036
            | exact resolve b8e30036 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30036
          have b8e30147 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op y (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b8e30012 X0 x x
               have i₂ := b8e30097 x x
               grind)
            | exact superpose b8e30097 b8e30012
            | exact resolve b8e30012 b8e30097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30012 b8e30097
          have b8e30150 : (σ (k x y)) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b8e30008
               have i₂ := b8e894
               grind)
            | exact superpose b8e894 b8e30008
            | exact resolve b8e30008 b8e894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e894 b8e30008
          have b8e30154 : ∀ X1 : G, (M.op (τ x) x) = (M.op (τ x) (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b8e30108 x X1
               have i₂ := b8e30064 x (M.op X1 X1)
               grind)
            | exact superpose b8e30064 b8e30108
            | exact resolve b8e30108 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30108
          have b8e30167 : ∀ X1 : G, (M.op (τ x) X1) = (M.op (M.op (τ x) x) X1) := by
            intro X1
            first
            | (have i₁ := b8e30129 x X1
               have i₂ := b8e30063 x X1
               grind)
            | exact superpose b8e30063 b8e30129
            | exact resolve b8e30129 b8e30063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30063 b8e30129
          have b8e30179 : (M.op y (M.op y x)) = (M.op (τ x) x) := by
            first
            | (have i₁ := b8e30147 x
               have i₂ := b8e30064 x x
               grind)
            | exact superpose b8e30064 b8e30147
            | exact resolve b8e30147 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30147
          have b8e30962 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X1) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e81 X0 x
               have i₂ := b8e194 X0 x X1
               grind)
            | exact superpose b8e194 b8e81
            | exact resolve b8e81 b8e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e31031 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ (M.op X2 X2)) (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X1) (σ X0))) (M.op (M.op X4 X4) (M.op X3 X3))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e175 X2 (σ X0) (M.op X3 X3) X4
               have i₂ := b8e194 X0 X3 X1
               grind)
            | exact superpose b8e194 b8e175
            | exact resolve b8e175 b8e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175 b8e194
          have b8e31159 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X2 X2)) (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X1) (σ X0))) (M.op (τ x) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e31031 X0 X1 X2 X3 x
               have i₂ := b8e30064 x (M.op X3 X3)
               grind)
            | exact superpose b8e30064 b8e31031
            | exact resolve b8e31031 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31031
          have b8e31184 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (τ (τ x)) (M.op (M.op X1 X1) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e30962 X0 X1
               have i₂ := b8e30079 X0 (M.op (M.op X1 X1) (σ X0))
               grind)
            | exact superpose b8e30079 b8e30962
            | exact resolve b8e30962 b8e30079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30962
          have b8e31471 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) (M.op (M.op X1 X1) (σ X0))) (M.op (τ x) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e31159 X0 X1 X2 x
               have i₂ := b8e30154 x
               grind)
            | exact superpose b8e30154 b8e31159
            | exact resolve b8e31159 b8e30154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31159
          have b8e31496 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (τ (τ x)) (M.op (τ x) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b8e31184 X0 x
               have i₂ := b8e30064 x (σ X0)
               grind)
            | exact superpose b8e30064 b8e31184
            | exact resolve b8e31184 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31184
          have b8e31773 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ X0)) = (M.op (M.op (τ (τ x)) (M.op (M.op X1 X1) (σ X0))) (M.op (τ x) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e31471 X0 X1 X2
               have i₂ := b8e30079 X0 (M.op (M.op X1 X1) (σ X0))
               grind)
            | exact superpose b8e30079 b8e31471
            | exact resolve b8e31471 b8e30079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31471
          have b8e31795 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (τ (τ x)) (M.op (τ x) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b8e31496 X0
               have i₂ := b8e30065 X0
               grind)
            | exact superpose b8e30065 b8e31496
            | exact resolve b8e31496 b8e30065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31496
          have b8e32033 : ∀ X0 X2 : G, (M.op (σ (M.op X2 X2)) (σ X0)) = (M.op (M.op (τ (τ x)) (M.op (τ x) (σ X0))) (M.op (τ x) x)) := by
            intro X0 X2
            first
            | (have i₁ := b8e31773 X0 x X2
               have i₂ := b8e30064 x (σ X0)
               grind)
            | exact superpose b8e30064 b8e31773
            | exact resolve b8e31773 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31773
          have b8e32200 : ∀ X0 X2 : G, (M.op (σ (M.op X2 X2)) (σ X0)) = (M.op (M.op (σ x) (σ X0)) (M.op (τ x) x)) := by
            intro X0 X2
            first
            | (have i₁ := b8e32033 X0 X2
               have i₂ := b8e31795 X0
               grind)
            | exact superpose b8e31795 b8e32033
            | exact resolve b8e32033 b8e31795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31795 b8e32033
          have b8e32296 : ∀ X0 : G, (M.op (τ (τ x)) (σ X0)) = (M.op (M.op (σ x) (σ X0)) (M.op (τ x) x)) := by
            intro X0
            first
            | (have i₁ := b8e32200 X0 x
               have i₂ := b8e30079 x (σ X0)
               grind)
            | exact superpose b8e30079 b8e32200
            | exact resolve b8e32200 b8e30079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32200
          have b8e33015 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X2) = (M.op (M.op X3 X2) (M.op (σ (M.op X4 X4)) X3)) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b8e201 X4 (M.op x x) X2 X3
               have i₂ := b8e291 X0 x x
               grind)
            | exact superpose b8e291 b8e201
            | exact resolve b8e201 b8e291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e201
          have b8e33115 : ∀ X0 X1 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (M.op X0 X0) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e4527 (M.op (σ y) (σ (M.op y y)))
               have i₂ := b8e291 y X0 X1
               grind)
            | exact superpose b8e291 b8e4527
            | exact resolve b8e4527 b8e291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e291
          have b8e33225 : ∀ X1 : G, (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (τ x) (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b8e33115 x X1
               have i₂ := b8e30064 x (M.op X1 X1)
               grind)
            | exact superpose b8e30064 b8e33115
            | exact resolve b8e33115 b8e30064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30064 b8e33115
          have b8e33316 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X2) = (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e33015 X0 X2 X3 x
               have i₂ := b8e30079 x X3
               grind)
            | exact superpose b8e30079 b8e33015
            | exact resolve b8e33015 b8e30079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30079 b8e33015
          have b8e33657 : (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ y) (σ (M.op y y))) (M.op (τ x) x)) := by
            first
            | (have i₁ := b8e33225 x
               have i₂ := b8e30154 x
               grind)
            | exact superpose b8e30154 b8e33225
            | exact resolve b8e33225 b8e30154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30154 b8e33225
          have b8e33748 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (M.op (σ x) (σ X0))) X2) = (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e33316 X0 X2 X3
               have i₂ := b8e30065 X0
               grind)
            | exact superpose b8e30065 b8e33316
            | exact resolve b8e33316 b8e30065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33316
          have b8e34085 : (M.op (σ x) (σ (M.op y x))) = (M.op (M.op (σ x) (σ y)) (M.op (τ x) x)) := by
            first
            | (have i₁ := b8e33657
               have i₂ := b8e30065 y
               grind)
            | exact superpose b8e30065 b8e33657
            | exact resolve b8e33657 b8e30065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33657
          have b8e34176 : ∀ X2 X3 : G, (M.op (M.op (σ x) (σ (M.op x x))) X2) = (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e33748 x X2 X3
               have i₂ := b8e139 x (σ x)
               grind)
            | exact superpose b8e139 b8e33748
            | exact resolve b8e33748 b8e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139 b8e33748
          have b8e34508 : (M.op (σ x) (σ (M.op y x))) = (M.op (τ (τ x)) (σ y)) := by
            first
            | (have i₁ := b8e34085
               have i₂ := b8e32296 y
               grind)
            | exact superpose b8e32296 b8e34085
            | exact resolve b8e34085 b8e32296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32296 b8e34085
          have b8e34558 : ∀ X2 X3 : G, (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) = (M.op (M.op (σ x) (σ x)) X2) := by
            intro X2 X3
            first
            | (have i₁ := b8e34176 X2 X3
               have i₂ := b8e30065 x
               grind)
            | exact superpose b8e30065 b8e34176
            | exact resolve b8e34176 b8e30065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30065 b8e34176
          have b8e34888 : ∀ X2 X3 : G, (M.op (M.op y (M.op y x)) X2) = (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e34558 X2 X3
               have i₂ := b8e30099 (σ x) X2
               grind)
            | exact superpose b8e30099 b8e34558
            | exact resolve b8e34558 b8e30099
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30099 b8e34558
          have b8e35184 : ∀ X2 X3 : G, (M.op (M.op (τ x) x) X2) = (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e34888 X2 X3
               have i₂ := b8e30179
               grind)
            | exact superpose b8e30179 b8e34888
            | exact resolve b8e34888 b8e30179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30179 b8e34888
          have b8e35448 : ∀ X2 X3 : G, (M.op (τ x) X2) = (M.op (M.op X3 X2) (M.op (τ (τ x)) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b8e35184 X2 X3
               have i₂ := b8e30167 X2
               grind)
            | exact superpose b8e30167 b8e35184
            | exact resolve b8e35184 b8e30167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30167 b8e35184
          have b8e39336 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) X0) (M.op (σ x) (σ (M.op y x)))) := by
            intro X0
            first
            | (have i₁ := b8e30009 (M.op (σ y) X0) X0
               have i₂ := b8e4527 X0
               grind)
            | exact superpose b8e4527 b8e30009
            | exact resolve b8e30009 b8e4527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4527
          have b8e39441 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b8e30009 y y
               have i₂ := b8e29689
               grind)
            | exact superpose b8e29689 b8e30009
            | exact resolve b8e30009 b8e29689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29689
          have b8e40092 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (σ y) X0) (M.op (τ (τ x)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b8e39336 X0
               have i₂ := b8e34508
               grind)
            | exact superpose b8e34508 b8e39336
            | exact resolve b8e39336 b8e34508
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34508 b8e39336
          have b8e40371 : ∀ X0 : G, (M.op x X0) = (M.op (τ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e40092 X0
               have i₂ := b8e35448 X0 (σ y)
               grind)
            | exact superpose b8e35448 b8e40092
            | exact resolve b8e40092 b8e35448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35448 b8e40092
          have b8e48159 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 (τ x))) := by
            intro X0
            first
            | (have i₁ := b8e30009 (τ x) X0
               have i₂ := b8e40371 (M.op X0 (τ x))
               grind)
            | exact superpose b8e40371 b8e30009
            | exact resolve b8e30009 b8e40371
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e48191 : (M.op (σ x) (σ (k x y))) = (M.op x (M.op (σ y) (τ x))) := by
            first
            | (have i₁ := b8e899 (τ x)
               have i₂ := b8e40371 (M.op (σ y) (τ x))
               grind)
            | exact superpose b8e40371 b8e899
            | exact resolve b8e899 b8e40371
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e899 b8e40371
          have b8e48198 : (σ (k x y)) = (M.op x (M.op (σ y) (τ x))) := by
            first
            | (have i₁ := b8e48191
               have i₂ := b8e30150
               grind)
            | exact superpose b8e30150 b8e48191
            | exact resolve b8e48191 b8e30150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30150 b8e48191
          have b8e48425 : (σ (k x y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e48198
               have i₂ := b8e48159 (σ y)
               grind)
            | exact superpose b8e48159 b8e48198
            | exact resolve b8e48198 b8e48159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48159 b8e48198
          have b8e161649 : (σ (M.op y x)) = (M.op x (σ y)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e48425
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e48425
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e48425 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48425
          have b8e161675 : (σ (M.op y x)) = (M.op x (σ y)) ∨ x = y := by
            first
            | (have r₁ := b8e161649
               have r₂ := b8e22
               grind)
            | exact resolve b8e161649 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161649
          have b8e161680 : (σ (M.op y x)) = (M.op x (σ y)) := by
            first
            | (have r₁ := b8e161675
               have r₂ := b8e21
               grind)
            | exact resolve b8e161675 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161675
          have b8e161684 : (σ (M.op x y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e161680
               have i₂ := b8e39441
               grind)
            | exact superpose b8e39441 b8e161680
            | exact resolve b8e161680 b8e39441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39441 b8e161680
          have b8e170971 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e30009 x X0
               have i₂ := b8e30025 x X0
               grind)
            | exact superpose b8e30025 b8e30009
            | exact resolve b8e30009 b8e30025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30009 b8e30025
          have b8e174779 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e170971 (σ y)
               grind)
            | exact superpose b8e170971 b8e20
            | exact resolve b8e20 b8e170971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e170971
          have b8e175146 : False := by grind
          exact b8e175146

/-- `Equation4474`: `x ◇ (y ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pyx_pxy_Equation4474 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4474 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4474.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e15 X0 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 X0 x
             grind)
          | (have r₁ := b0e15 X0 x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e27 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b0e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24
        have b0e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 (τ X0) X1
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e18
          | exact resolve b0e18 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X0 X1 X3
             have i₂ := b0e12 X0 X1 X2
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e12 x x x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X0 X1 (M.op X2 X2)
             have i₂ := b0e12 (M.op X0 X1) X2 X3
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e41 X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e41
          | exact resolve b0e41 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e89 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e17 X2 X0
             grind)
          | exact superpose b0e17 b0e16
          | (have j0 := b0e16 X0 X1
             have j1 := b0e17 X1 X1
             grind)
          | (have r₁ := b0e16 X1 X1
             have r₂ := b0e17 X0 X1
             grind)
          | (have r₁ := b0e16 X0 X1
             have r₂ := b0e17 X0 X1
             grind)
          | exact resolve b0e16 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e108 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b0e89 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e89
        have b0e127 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b0e29 X0 x
             have i₂ := b0e27 (τ X0)
             grind)
          | exact superpose b0e27 b0e29
          | exact resolve b0e29 b0e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e27 b0e29
        have b0e133 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b0e127 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e127
          | exact resolve b0e127 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e127
        have b0e227 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b0e12 (M.op X0 X1) X3 X4
             have i₂ := b0e36 X0 X1 (M.op X3 X3) X2
             grind)
          | (have i₁ := b0e12 (M.op X0 X1) X3 X4
             have i₂ := b0e36 X0 X1 X2 (M.op X3 X3)
             grind)
          | exact superpose b0e36 b0e12
          | exact resolve b0e12 b0e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e3825 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e108 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e108
        have b0e3826 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b0e3825 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3825
        have b0e3827 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e3826 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3826
        have b0e5411 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e133 (σ x)
             have i₂ := b0e3827 (σ x)
             grind)
          | exact superpose b0e3827 b0e133
          | (have j1 := b0e3827 (σ x)
             grind)
          | exact resolve b0e133 b0e3827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e133 b0e3827
        have b0e5436 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e5411
        have b0e5514 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e43 (σ x) (σ x) x x
             have i₂ := b0e5436
             grind)
          | exact superpose b0e5436 b0e43
          | exact resolve b0e43 b0e5436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43
        have b0e5528 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e5514 X0 X1
             have i₂ := b0e5436
             grind)
          | exact superpose b0e5436 b0e5514
          | exact resolve b0e5514 b0e5436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e5514
        have b0e5858 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e227 (σ x) (σ x) X2 x x
             have i₂ := b0e5436
             grind)
          | exact superpose b0e5436 b0e227
          | exact resolve b0e227 b0e5436
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e227 b0e5436
        have b0e6194 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e5858 X0 x x
             have i₂ := b0e5528 x x
             grind)
          | exact superpose b0e5528 b0e5858
          | exact resolve b0e5858 b0e5528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e5528 b0e5858
        have b0e6258 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e6194 (σ y)
             grind)
          | exact superpose b0e6194 b0e19
          | exact resolve b0e19 b0e6194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e6194
        have b0e6330 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e6258
             have i₂ := b0e48 y
             grind)
          | exact superpose b0e48 b0e6258
          | exact resolve b0e6258 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48 b0e6258
        have b0e6331 : False := by grind
        exact b0e6331
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b1e23 : x ≠ (M.op x x) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b1e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X0 X1 X3
               have i₂ := b1e13 X0 X1 X2
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e49 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b1e54 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b1e49 X0
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e49
            | exact resolve b1e49 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49
          have b1e68 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e17 (σ y) X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e17
            | (have j0 := b1e17 (σ y) X0
               grind)
            | (have r₁ := b1e17 (σ y) x
               have r₂ := b1e22
               grind)
            | exact resolve b1e17 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e70 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b1e17 y X0
               have i₂ := b1e54 y
               grind)
            | exact superpose b1e54 b1e17
            | (have j0 := b1e17 y X0
               grind)
            | (have r₁ := b1e17 y x
               have r₂ := b1e54 y
               grind)
            | exact resolve b1e17 b1e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e54
          have b1e71 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b1e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e70
          have b1e73 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b1e68 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e68
          have b1e107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X0 X1
               have i₂ := b1e18 (σ X0) (σ X1)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X1)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e129 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e14 (k X0 (τ X1))
               have i₂ := b1e30 X1 X0
               grind)
            | exact superpose b1e30 b1e14
            | exact resolve b1e14 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e427 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e16 X1 X0
               have i₂ := b1e73 X0
               grind)
            | exact superpose b1e73 b1e16
            | (have j0 := b1e16 X1 X0
               have j1 := b1e73 X0
               grind)
            | (have r₁ := b1e16 X0 X0
               have r₂ := b1e73 X0
               grind)
            | exact resolve b1e16 b1e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e73
          have b1e450 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0 X1
            first
            | (have j0 := b1e427 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e427
          have b1e4764 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b1e107 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e107
          have b1e4765 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b1e4764 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e4764
          have b1e4937 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e44 X0 X0 X2 x
               have i₂ := b1e71 X0
               grind)
            | exact superpose b1e71 b1e44
            | (have j1 := b1e71 X0
               grind)
            | exact resolve b1e44 b1e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e44
          have b1e8594 : ∀ X0 X1 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (k X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e19 y X0
               have i₂ := b1e450 (σ X0) X1
               grind)
            | exact superpose b1e450 b1e19
            | (have j1 := b1e450 (σ X0) X1
               grind)
            | exact resolve b1e19 b1e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e450
          have b1e15625 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b1e4765 (τ X0)
               have i₂ := b1e30 X0 (τ X0)
               grind)
            | exact superpose b1e30 b1e4765
            | (have j0 := b1e4765 (τ X0)
               grind)
            | exact resolve b1e4765 b1e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e30 b1e4765
          have b1e15667 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b1e15625 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e15625
            | (have j0 := b1e15625 X0
               grind)
            | exact resolve b1e15625 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15625
          have b1e15692 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e15667 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e15667
            | (have j0 := b1e15667 X0
               grind)
            | exact resolve b1e15667 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15667
          have b1e376546 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x y) = (k y x) := by
            intro X0
            first
            | (have i₁ := b1e23
               have i₂ := b1e4937 x x X0
               grind)
            | (have i₁ := b1e23
               have i₂ := b1e4937 x X0 x
               grind)
            | exact superpose b1e4937 b1e23
            | (have j1 := b1e4937 x x x
               grind)
            | exact resolve b1e23 b1e4937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e376563 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e71 X0
               have i₂ := b1e4937 X0 X0 X1
               grind)
            | (have i₁ := b1e71 X0
               have i₂ := b1e4937 X0 X1 X0
               grind)
            | exact superpose b1e4937 b1e71
            | (have j0 := b1e71 X0
               have j1 := b1e4937 X0 X1 x
               grind)
            | exact resolve b1e71 b1e4937
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e71 b1e4937
          have b1e377054 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have j0 := b1e376563 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e376563
          have b1e377080 : (M.op x y) = (k y x) := by
            first
            | (have j1 := b1e377054 x x
               grind)
            | (have r₁ := b1e376546 x
               have r₂ := b1e377054 x x
               grind)
            | exact resolve b1e376546 b1e377054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e376546 b1e377054
          have b1e1289356 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e20
               have i₂ := b1e8594 x X0
               grind)
            | exact superpose b1e8594 b1e20
            | (have j1 := b1e8594 x X0
               grind)
            | exact resolve b1e20 b1e8594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e8594
          have b1e1289388 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e1289356 X0
               have i₂ := b1e377080
               grind)
            | exact superpose b1e377080 b1e1289356
            | (have j0 := b1e1289356 X0
               grind)
            | exact resolve b1e1289356 b1e377080
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e377080 b1e1289356
          have b1e1289389 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b1e1289388 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1289388
          have b1e1289439 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
            intro X0
            first
            | (have i₁ := b1e129 X0 (σ x)
               have i₂ := b1e1289389 (σ X0)
               grind)
            | exact superpose b1e1289389 b1e129
            | exact resolve b1e129 b1e1289389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e129 b1e1289389
          have b1e1289467 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b1e1289439 X0
               have i₂ := b1e14 x
               grind)
            | exact superpose b1e14 b1e1289439
            | exact resolve b1e1289439 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1289439
          have b1e1289479 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b1e1289467 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e1289467
            | exact resolve b1e1289467 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1289467
          have b1e1289529 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have i₁ := b1e15692 x
               have i₂ := b1e1289479 x
               grind)
            | exact superpose b1e1289479 b1e15692
            | (have j0 := b1e15692 x
               grind)
            | (have r₁ := b1e15692 x
               have r₂ := b1e1289479 x
               grind)
            | exact resolve b1e15692 b1e1289479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e15692 b1e1289479
          have b1e1289571 : x = (M.op x x) := by grind
          clear b1e1289529
          have b1e1289590 : False := by grind
          exact b1e1289590
        · have b2e21 : y = (M.op y y) := by grind
          have b2e24 : y ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : False := by grind
          exact b2e25
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e40 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ x) (σ x) x
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e41 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e13 x x x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e48 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e41 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e41
            | exact resolve b3e41 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e41
          have b3e49 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b3e40 X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e40
            | exact resolve b3e40 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40
          have b3e120 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e49 (σ y)
               grind)
            | exact superpose b3e49 b3e20
            | exact resolve b3e20 b3e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e49
          have b3e130 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e120
               have i₂ := b3e48 y
               grind)
            | exact superpose b3e48 b3e120
            | exact resolve b3e120 b3e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e48 b3e120
          have b3e131 : False := by grind
          exact b3e131
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b4e17 X0 y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e17
              | (have j0 := b4e17 X0 y
                 grind)
              | (have r₁ := b4e17 X0 y
                 have r₂ := b4e26
                 grind)
              | exact resolve b4e17 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b4e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e27
            have b4e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b4e20 (τ X0) X1
                 have i₂ := b4e16 X0
                 grind)
              | exact superpose b4e16 b4e20
              | exact resolve b4e20 b4e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e101 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b4e23
                 have i₂ := b4e19 (σ y) X0
                 grind)
              | exact superpose b4e19 b4e23
              | (have j1 := b4e19 X0 X0
                 grind)
              | (have r₁ := b4e23
                 have r₂ := b4e19 X0 (σ y)
                 grind)
              | (have r₁ := b4e23
                 have r₂ := b4e19 (σ y) x
                 grind)
              | exact resolve b4e23 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have j0 := b4e101 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e101
            have b4e124 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b4e31 X0 y
                 have i₂ := b4e30 (τ X0)
                 grind)
              | exact superpose b4e30 b4e31
              | exact resolve b4e31 b4e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30 b4e31
            have b4e135 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b4e124 X0
                 have i₂ := b4e16 X0
                 grind)
              | exact superpose b4e16 b4e124
              | exact resolve b4e124 b4e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e124
            have b4e481 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e135 (σ y)
                 have i₂ := b4e105 (σ y)
                 grind)
              | exact superpose b4e105 b4e135
              | (have j1 := b4e105 (σ y)
                 grind)
              | exact resolve b4e135 b4e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e105 b4e135
            have b4e486 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b4e481
            have b4e492 : False := by grind
            exact b4e492
          · have b5e22 : y = (M.op y y) := by grind
            have b5e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : False := by grind
            exact b5e27
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e16
            | (have j0 := b6e16 X0 x
               grind)
            | (have r₁ := b6e16 X0 x
               have r₂ := b6e24
               grind)
            | exact resolve b6e16 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e27 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b6e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26
          have b6e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e96 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 X0 X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 X0 (σ x)
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) x
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e100 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b6e96 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e96
          have b6e113 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e29 X0 x
               have i₂ := b6e27 (τ X0)
               grind)
            | exact superpose b6e27 b6e29
            | exact resolve b6e29 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27 b6e29
          have b6e120 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e113 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e113
            | exact resolve b6e113 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e113
          have b6e378 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e120 (σ x)
               have i₂ := b6e100 (σ x)
               grind)
            | exact superpose b6e100 b6e120
            | (have j1 := b6e100 (σ x)
               grind)
            | exact resolve b6e120 b6e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e100 b6e120
          have b6e382 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e378
          have b6e386 : False := by grind
          exact b6e386
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b7e17 X0 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e17
              | (have j0 := b7e17 X0 y
                 grind)
              | (have r₁ := b7e17 X0 y
                 have r₂ := b7e26
                 grind)
              | exact resolve b7e17 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e28 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b7e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e27
            have b7e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b7e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e29 X0 y
                 have i₂ := b7e28 (τ X0)
                 grind)
              | exact superpose b7e28 b7e29
              | exact resolve b7e29 b7e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e28 b7e29
            have b7e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b7e32 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e32
              | exact resolve b7e32 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e32
            have b7e91 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b7e23
                 have i₂ := b7e19 (σ y) X0
                 grind)
              | exact superpose b7e19 b7e23
              | (have j1 := b7e19 X0 X0
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 X0 (σ y)
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 (σ y) x
                 grind)
              | exact resolve b7e23 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e98 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
              intro X0
              first
              | (have j0 := b7e91 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e91
            have b7e360 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e36 (σ y)
                 have i₂ := b7e98 (σ y)
                 grind)
              | exact superpose b7e98 b7e36
              | (have j1 := b7e98 (σ y)
                 grind)
              | exact resolve b7e36 b7e98
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e98
            have b7e363 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b7e360
            have b7e367 : False := by grind
            exact b7e367
          · have b8e22 : y = (M.op y y) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : False := by grind
            exact b8e27
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 X0 (σ y)
               grind)
            | (have r₁ := b9e16 X0 (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e27 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b9e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e27 (σ X0)
               grind)
            | exact superpose b9e27 b9e19
            | exact resolve b9e19 b9e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b9e14 (k X0 y)
               have i₂ := b9e32 X0
               grind)
            | exact superpose b9e32 b9e14
            | exact resolve b9e14 b9e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e36 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b9e35 X0
               have i₂ := b9e14 X0
               grind)
            | exact superpose b9e14 b9e35
            | exact resolve b9e35 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e35
          have b9e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b9e17 X0 X1
               have i₂ := b9e18 X2 X0
               grind)
            | exact superpose b9e18 b9e17
            | (have j0 := b9e17 X0 X1
               have j1 := b9e18 X1 X1
               grind)
            | (have r₁ := b9e17 X1 X1
               have r₂ := b9e18 X0 X1
               grind)
            | (have r₁ := b9e17 X0 X1
               have r₂ := b9e18 X0 X1
               grind)
            | exact resolve b9e17 b9e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e101 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b9e81 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e81
          have b9e3534 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e101 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e101
          have b9e3535 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e3534 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3534
          have b9e3536 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e3535 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3535
          have b9e5206 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b9e36 y
               have i₂ := b9e3536 y
               grind)
            | exact superpose b9e3536 b9e36
            | (have j1 := b9e3536 y
               grind)
            | exact resolve b9e36 b9e3536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e36 b9e3536
          have b9e5211 : y = (M.op y y) := by grind
          clear b9e5206
          have b9e5265 : False := by grind
          exact b9e5265
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e23 : x = (M.op x x) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e23 : x = (M.op x x) := by grind
            have b11e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : False := by grind
            exact b11e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ x)) := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e42 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b12e14 (σ x) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e43 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b12e14 x x x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e48 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b12e43 X0
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e43
              | exact resolve b12e43 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e43
            have b12e49 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b12e42 X0
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e42
              | exact resolve b12e42 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e70 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e49 (σ y)
                 grind)
              | exact superpose b12e49 b12e21
              | exact resolve b12e21 b12e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e49
            have b12e80 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e70
                 have i₂ := b12e48 y
                 grind)
              | exact superpose b12e48 b12e70
              | exact resolve b12e70 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e48 b12e70
            have b12e81 : False := by grind
            exact b12e81
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e24 : x = (M.op x x) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e24 : x = (M.op x x) := by grind
              have b14e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : False := by grind
              exact b14e29
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 X0 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e17
              | (have j0 := b15e17 X0 x
                 grind)
              | (have r₁ := b15e17 X0 x
                 have r₂ := b15e26
                 grind)
              | exact resolve b15e17 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e28 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27
            have b15e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 (τ X0) X1
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e29 X0 x
                 have i₂ := b15e28 (τ X0)
                 grind)
              | exact superpose b15e28 b15e29
              | exact resolve b15e29 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e29
            have b15e36 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b15e32 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e32
              | exact resolve b15e32 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e32
            have b15e92 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 X0 X0
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 X0 (σ x)
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) x
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e97 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have j0 := b15e92 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e92
            have b15e318 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e36 (σ x)
                 have i₂ := b15e97 (σ x)
                 grind)
              | exact superpose b15e97 b15e36
              | (have j1 := b15e97 (σ x)
                 grind)
              | exact resolve b15e36 b15e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36 b15e97
            have b15e321 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e318
            have b15e325 : False := by grind
            exact b15e325
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e24 : x = (M.op x x) := by grind
              have b16e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e24 : x = (M.op x x) := by grind
              have b17e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : False := by grind
              exact b17e29
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e22 : x ≠ (M.op x x) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e25 : False := by grind
          exact b18e25
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e22 : y ≠ (M.op y y) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b20e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | (have r₁ := b20e17 X0 (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27
            have b20e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e28 (σ X0)
                 have i₂ := b20e20 X0 y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e32 X0
                 grind)
              | exact superpose b20e32 b20e15
              | exact resolve b20e15 b20e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e35 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e35
              | exact resolve b20e35 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e103 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b20e36 X0
                 have i₂ := b20e19 X0 y
                 grind)
              | exact superpose b20e19 b20e36
              | (have j1 := b20e19 y y
                 grind)
              | exact resolve b20e36 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e111 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e103 X0
                 grind)
              | (have r₁ := b20e103 y
                 have r₂ := b20e26
                 grind)
              | (have r₁ := b20e103 X0
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e103 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e103
            have b20e2744 : y ≠ y ∨ y = (M.op y y) := by
              first
              | (have j0 := b20e111 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e111
            have b20e2745 : y = (M.op y y) := by grind
            clear b20e2744
            have b20e2757 : False := by grind
            exact b20e2757
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e23 : x ≠ (M.op x x) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : False := by grind
            exact b21e27
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e23 : y ≠ (M.op y y) := by grind
              have b22e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : False := by grind
              exact b22e29
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              have b23e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e18 X0 (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | (have j0 := b23e18 X0 (σ x)
                   grind)
                | (have r₁ := b23e18 X0 (σ x)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e30 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b23e29 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29
              have b23e34 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e30 (σ X0)
                   grind)
                | exact superpose b23e30 b23e21
                | exact resolve b23e21 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30
              have b23e37 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e16 (k X0 x)
                   have i₂ := b23e34 X0
                   grind)
                | exact superpose b23e34 b23e16
                | exact resolve b23e16 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34
              have b23e38 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e37 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e37
                | exact resolve b23e37 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e41 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 (σ x) X1
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X0 X1 X3
                   have i₂ := b23e15 X0 X1 X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e93 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b23e25
                   have i₂ := b23e20 (σ y) X0
                   grind)
                | exact superpose b23e20 b23e25
                | (have j1 := b23e20 X0 X0
                   grind)
                | (have r₁ := b23e25
                   have r₂ := b23e20 X0 (σ y)
                   grind)
                | (have r₁ := b23e25
                   have r₂ := b23e20 (σ y) x
                   grind)
                | exact resolve b23e25 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e98 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
                intro X0
                first
                | (have j0 := b23e93 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e93
              have b23e156 : ∀ X0 X1 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (k X1 (M.op X0 (σ x))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e18 X1 (M.op X0 (σ x))
                   have i₂ := b23e41 X0 (M.op X0 (σ x))
                   grind)
                | exact superpose b23e41 b23e18
                | (have j0 := b23e18 X1 (M.op X0 (σ x))
                   grind)
                | (have r₁ := b23e18 X0 (M.op X0 (σ x))
                   have r₂ := b23e41 X0 (M.op X0 (σ x))
                   grind)
                | exact resolve b23e18 b23e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41
              have b23e159 : ∀ X0 X1 : G, (k X1 (M.op X0 (σ x))) = X1 := by
                intro X0 X1
                first
                | (have j0 := b23e156 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e156
              have b23e216 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X0 X1) X2)) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e159 (M.op X0 X1) X3
                   have i₂ := b23e44 X0 X1 (σ x) X2
                   grind)
                | (have i₁ := b23e159 (M.op X0 X1) X3
                   have i₂ := b23e44 X0 X1 X2 (σ x)
                   grind)
                | exact superpose b23e44 b23e159
                | exact resolve b23e159 b23e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e44 b23e159
              have b23e491 : (σ y) = (M.op (σ y) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e38 (σ y)
                   have i₂ := b23e98 x
                   grind)
                | exact superpose b23e98 b23e38
                | (have j1 := b23e98 x
                   grind)
                | exact resolve b23e38 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e496 : (σ y) = (M.op (σ y) x) := by
                first
                | (have r₁ := b23e491
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e491 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e491
              have b23e558 : ∀ X0 X1 : G, (k X0 (M.op (σ y) X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b23e216 (σ y) x X1 X0
                   have i₂ := b23e496
                   grind)
                | exact superpose b23e496 b23e216
                | exact resolve b23e216 b23e496
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e216
              have b23e802 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e558 X0 x
                   have i₂ := b23e496
                   grind)
                | exact superpose b23e496 b23e558
                | exact resolve b23e558 b23e496
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e496 b23e558
              have b23e1078 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e98 (σ y)
                   have i₂ := b23e802 (σ y)
                   grind)
                | exact superpose b23e802 b23e98
                | (have j0 := b23e98 (σ y)
                   grind)
                | exact resolve b23e98 b23e802
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e98 b23e802
              have b23e1081 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b23e1078
              have b23e1085 : False := by grind
              exact b23e1085
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e23 : x ≠ (M.op x x) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : False := by grind
            exact b24e27
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e23 : y ≠ (M.op y y) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X0 X1 X3
                   have i₂ := b26e15 X0 X1 X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e78 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 X0 X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 X0 (σ x)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) x
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e82 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0
                first
                | (have j0 := b26e78 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e78
              have b26e266 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e33 X0 X0 X2 x
                   have i₂ := b26e82 X0
                   grind)
                | exact superpose b26e82 b26e33
                | (have j1 := b26e82 X0
                   grind)
                | exact resolve b26e33 b26e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e20375 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e266 (σ y) (σ y) X0
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e266 (σ y) X0 (σ y)
                   grind)
                | exact superpose b26e266 b26e25
                | (have j1 := b26e266 (σ y) x x
                   grind)
                | exact resolve b26e25 b26e266
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e20408 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e82 X0
                   have i₂ := b26e266 X0 X0 X1
                   grind)
                | (have i₁ := b26e82 X0
                   have i₂ := b26e266 X0 X1 X0
                   grind)
                | exact superpose b26e266 b26e82
                | (have j0 := b26e82 X0
                   have j1 := b26e266 X0 X1 x
                   grind)
                | exact resolve b26e82 b26e266
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e82 b26e266
              have b26e20678 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
                intro X0 X1
                first
                | (have j0 := b26e20408 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20408
              have b26e20702 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j1 := b26e20678 (σ y) x
                   grind)
                | (have r₁ := b26e20375 x
                   have r₂ := b26e20678 (σ y) x
                   grind)
                | exact resolve b26e20375 b26e20678
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20375 b26e20678
              have b26e20707 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e20702
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e20702
                | exact resolve b26e20702 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20702
              have b26e22794 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e20707
                   grind)
                | exact superpose b26e20707 b26e22
                | exact resolve b26e22 b26e20707
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20707
              have b26e26739 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b26e22794
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e22794
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e22794 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e22794
              have b26e26753 : y = (M.op y y) ∨ x = (M.op x x) := by grind
              clear b26e26739
              have b26e26759 : x = (M.op x x) := by
                first
                | (have r₁ := b26e26753
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e26753 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e26753
              have b26e26760 : False := by grind
              exact b26e26760

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation4478 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4478 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
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
      have b0e96 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e103 : False := by grind
      exact b0e103
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
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b4e73 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) X0
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = X0 ∨ (k X0 y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e83 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e73 X0
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e73
            | (have j0 := b4e73 X0
               grind)
            | exact resolve b4e73 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e1651 : x = y ∨ (M.op x y) = (k x y) := by
            first
            | (have j0 := b4e75 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e1652 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e1651
               have r₂ := b4e21
               grind)
            | exact resolve b4e1651 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1651
          have b4e2645 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e83 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e83
            | (have j0 := b4e83 (σ X0)
               grind)
            | (have r₁ := b4e83 (σ x)
               have r₂ := b4e30 x
               grind)
            | exact resolve b4e83 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e83
          have b4e2655 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e2645 X0
               have i₂ := b4e19 X0 y
               grind)
            | exact superpose b4e19 b4e2645
            | (have j0 := b4e2645 X0
               grind)
            | exact resolve b4e2645 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2645
          have b4e252043 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b4e2655 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2655
          have b4e252050 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b4e252043
               have r₂ := b4e23
               grind)
            | exact resolve b4e252043 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e252043
          have b4e252051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e252050
               have i₂ := b4e1652
               grind)
            | exact superpose b4e1652 b4e252050
            | exact resolve b4e252050 b4e1652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1652 b4e252050
          have b4e252052 : False := by grind
          exact b4e252052
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
          have b5e62 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e62
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e62
            | exact resolve b5e62 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e66 : False := by grind
          exact b5e66
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
          have b7e65 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e65
            | exact resolve b7e65 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e65
          have b7e84 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e14
            | exact resolve b7e14 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e85 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e84
            | exact resolve b7e84 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e89 : False := by grind
          exact b7e89
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
          have b8e61 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e61
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e61
            | exact resolve b8e61 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e105 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
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
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e110 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e108 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e108
            | (have j0 := b8e108 X0 X1
               grind)
            | exact resolve b8e108 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e108
          have b8e1137 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e105 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e1138 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e1137
               have r₂ := b8e21
               grind)
            | exact resolve b8e1137 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1137
          have b8e2536 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e110 x y
               grind)
            | exact superpose b8e110 b8e20
            | (have j1 := b8e110 y x
               grind)
            | exact resolve b8e20 b8e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e2597 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e2536
               have r₂ := b8e64
               grind)
            | exact resolve b8e2536 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e2536
          have b8e2616 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e2597
               have r₂ := b8e23
               grind)
            | exact resolve b8e2597 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2597
          have b8e2631 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e2616
               have i₂ := b8e1138
               grind)
            | exact superpose b8e1138 b8e2616
            | exact resolve b8e2616 b8e1138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1138 b8e2616
          have b8e2632 : False := by grind
          exact b8e2632

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation4478 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
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
      have b0e96 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e103 : False := by grind
      exact b0e103
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
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b4e78 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ y) X0
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = X0 ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 y X0
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e82 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e78 X0
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e78
            | (have j0 := b4e78 X0
               grind)
            | exact resolve b4e78 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e1685 : x = y ∨ (M.op x y) = (k y x) := by
            first
            | (have j0 := b4e80 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e1686 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e1685
               have r₂ := b4e21
               grind)
            | exact resolve b4e1685 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1685
          have b4e2335 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ X0) = (σ y) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e82 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e82
            | (have j0 := b4e82 (σ X0)
               grind)
            | (have r₁ := b4e82 (σ x)
               have r₂ := b4e30 x
               grind)
            | exact resolve b4e82 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e82
          have b4e2345 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e2335 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e2335
            | (have j0 := b4e2335 X0
               grind)
            | exact resolve b4e2335 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2335
          have b4e250928 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b4e2345 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2345
          have b4e250935 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b4e250928
               have r₂ := b4e23
               grind)
            | exact resolve b4e250928 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e250928
          have b4e250936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e250935
               have i₂ := b4e1686
               grind)
            | exact superpose b4e1686 b4e250935
            | exact resolve b4e250935 b4e1686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1686 b4e250935
          have b4e250937 : False := by grind
          exact b4e250937
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
          have b5e62 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e62
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e62
            | exact resolve b5e62 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e66 : False := by grind
          exact b5e66
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
          have b7e65 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e65
            | exact resolve b7e65 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e65
          have b7e84 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e14
            | exact resolve b7e14 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e85 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e84
            | exact resolve b7e84 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e89 : False := by grind
          exact b7e89
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
          have b8e61 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e61
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e61
            | exact resolve b8e61 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e95 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
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
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e108 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e108
            | (have j0 := b8e108 X0 X1
               grind)
            | exact resolve b8e108 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e108
          have b8e1111 : (M.op x y) = (k x y) ∨ x = y := by
            first
            | (have j0 := b8e95 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95
          have b8e1112 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e1111
               have r₂ := b8e21
               grind)
            | exact resolve b8e1111 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1111
          have b8e2536 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e110 x y
               grind)
            | exact superpose b8e110 b8e20
            | (have j1 := b8e110 y x
               grind)
            | exact resolve b8e20 b8e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e2597 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e2536
               have r₂ := b8e64
               grind)
            | exact resolve b8e2536 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e2536
          have b8e2616 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e2597
               have r₂ := b8e23
               grind)
            | exact resolve b8e2597 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2597
          have b8e2631 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e2616
               have i₂ := b8e1112
               grind)
            | exact superpose b8e1112 b8e2616
            | exact resolve b8e2616 b8e1112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1112 b8e2616
          have b8e2632 : False := by grind
          exact b8e2632

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation4478 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4478 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e38 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X0 (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e39 x X2
               have i₂ := b4e39 x X0
               grind)
            | exact superpose b4e39 b4e39
            | exact resolve b4e39 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e278 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (σ x) X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e38 x X2
               have i₂ := b4e38 x X0
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e313 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e278 (σ y) X0
               grind)
            | (have i₁ := b4e20
               have i₂ := b4e278 X0 (σ y)
               grind)
            | exact superpose b4e278 b4e20
            | exact resolve b4e20 b4e278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e314 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b4e30 x
               have i₂ := b4e278 (σ x) X0
               grind)
            | (have i₁ := b4e30 x
               have i₂ := b4e278 X0 (σ x)
               grind)
            | exact superpose b4e278 b4e30
            | exact resolve b4e30 b4e278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e278
          have b4e324 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e313 x
               have i₂ := b4e314 x
               grind)
            | exact superpose b4e314 b4e313
            | exact resolve b4e313 b4e314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e313 b4e314
          have b4e633 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e324
               have i₂ := b4e44 y X0
               grind)
            | (have i₁ := b4e324
               have i₂ := b4e44 X0 y
               grind)
            | exact superpose b4e44 b4e324
            | exact resolve b4e324 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e324
          have b4e820 : False := by grind
          exact b4e820
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e54 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e56 : x = y ∨ x = (k x y) := by grind
          clear b5e54
          have b5e57 : x = (k x y) := by
            first
            | (have r₁ := b5e56
               have r₂ := b5e21
               grind)
            | exact resolve b5e56 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e1368 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e61241 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1368 y x
               have i₂ := b5e57
               grind)
            | exact superpose b5e57 b5e1368
            | (have j0 := b5e1368 y x
               grind)
            | exact resolve b5e1368 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57 b5e1368
          have b5e61244 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e61241
          have b5e61247 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e61244
               have r₂ := b5e24
               grind)
            | exact resolve b5e61244 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61244
          have b5e61251 : False := by grind
          exact b5e61251
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e48 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          clear b7e53
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
          have b7e67 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e68 : x = (M.op y x) ∨ x = y := by grind
          clear b7e67
          have b7e70 : x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e72 : False := by grind
          exact b7e72
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e1168 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1168
               have r₂ := b8e23
               grind)
            | exact resolve b8e1168 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1168
          have b8e37009 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e1184
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1184
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e1184
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1184
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1184 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37010 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e37009
          have b8e37011 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e37010
               have r₂ := b8e21
               grind)
            | exact resolve b8e37010 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37010
          have b8e37013 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e37011
               grind)
            | exact superpose b8e37011 b8e20
            | exact resolve b8e20 b8e37011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37016 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e37011
               grind)
            | exact superpose b8e37011 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e37011
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e37011
               grind)
            | exact resolve b8e17 b8e37011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37011
          have b8e37062 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e37016
          have b8e37069 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e37062
               have r₂ := b8e23
               grind)
            | exact resolve b8e37062 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37062
          have b8e37071 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e37069
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e37069
            | exact resolve b8e37069 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37069
          have b8e38836 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e37071
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e37071
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e37071 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37071
          have b8e38860 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e38836
          have b8e38877 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e38860
               have r₂ := b8e37013
               grind)
            | exact resolve b8e38860 b8e37013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37013 b8e38860
          have b8e38878 : y = (M.op x y) := by
            first
            | (have r₁ := b8e38877
               have r₂ := b8e21
               grind)
            | exact resolve b8e38877 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38877
          have b8e40443 : y ≠ y ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e38878
               grind)
            | exact superpose b8e38878 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e38878
               grind)
            | exact resolve b8e17 b8e38878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40491 : x = y ∨ y = (k y x) := by grind
          clear b8e40443
          have b8e40492 : y = (k y x) := by
            first
            | (have r₁ := b8e40491
               have r₂ := b8e21
               grind)
            | exact resolve b8e40491 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40491
          have b8e42088 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1184
               have i₂ := b8e40492
               grind)
            | exact superpose b8e40492 b8e1184
            | exact resolve b8e1184 b8e40492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1184 b8e40492
          have b8e42092 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e42088
               have i₂ := b8e38878
               grind)
            | exact superpose b8e38878 b8e42088
            | exact resolve b8e42088 b8e38878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42088
          have b8e42093 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e42092
          have b8e43727 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e42093
               grind)
            | exact superpose b8e42093 b8e20
            | exact resolve b8e20 b8e42093
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42093
          have b8e43789 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e43727
               have i₂ := b8e38878
               grind)
            | exact superpose b8e38878 b8e43727
            | exact resolve b8e43727 b8e38878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38878 b8e43727
          have b8e43790 : False := by grind
          exact b8e43790
