import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b5e45 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e48 : x = y ∨ y = (k x y) := by grind
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
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e159 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e4375 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e159 x y
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e159
            | (have j0 := b5e159 x y
               grind)
            | exact resolve b5e159 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e159
          have b5e4378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e4375
          have b5e4381 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e4378
               have r₂ := b5e24
               grind)
            | exact resolve b5e4378 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4378
          have b5e4385 : False := by grind
          exact b5e4385
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
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
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
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e46 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e57 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e47
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e47 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e58 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e26
               grind)
            | exact resolve b7e57 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e57
          have b7e59 : x = y := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e22
               grind)
            | exact resolve b7e58 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e60 : False := by grind
          exact b7e60
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e130 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e55 x y
               grind)
            | exact superpose b8e55 b8e20
            | (have j1 := b8e55 x y
               grind)
            | exact resolve b8e20 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e130
               have r₂ := b8e24
               grind)
            | exact resolve b8e130 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e144 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e138
               have r₂ := b8e23
               grind)
            | exact resolve b8e138 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e144
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e144
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e144
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e144
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e144 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144
          have b8e148 : y = (M.op x y) ∨ x = y := by grind
          clear b8e147
          have b8e149 : x = y := by
            first
            | (have r₁ := b8e148
               have r₂ := b8e22
               grind)
            | exact resolve b8e148 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148
          have b8e150 : False := by grind
          exact b8e150

/-- `Equation310`: `x ◇ x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pyx_Equation310 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law310 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law310.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1
          grind
        have b0e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y y) := by grind
        have b0e21 : (σ x) = (M.op (σ y) (σ y)) := by grind
        have b0e22 : y = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e29 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e12 X0 X2
             have i₂ := b0e12 X0 X1
             grind)
          | (have i₁ := b0e12 (M.op X1 X1) X1
             have i₂ := b0e12 (M.op X1 X1) X1
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e32 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e12 X0 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e33 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b0e12 X0 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b0e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b0e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1
             have i₂ := b0e32 X0
             grind)
          | (have i₁ := b0e12 y X1
             have i₂ := b0e32 y
             grind)
          | exact superpose b0e32 b0e12
          | exact resolve b0e12 b0e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e42 : ∀ X0 : G, (k (M.op X0 y) X0) = X0 := by
          intro X0
          grind
        have b0e44 : y = (M.op x y) := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e32 x
             grind)
          | exact superpose b0e32 b0e22
          | exact resolve b0e22 b0e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b0e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b0e46 X0
             have i₂ := b0e33 (σ X0)
             grind)
          | exact superpose b0e33 b0e46
          | (have j0 := b0e46 X0
             grind)
          | exact resolve b0e46 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e46
        have b0e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) x) := by
          intro X0
          first
          | (have i₁ := b0e47 X0
             have i₂ := b0e33 (σ X0)
             grind)
          | exact superpose b0e33 b0e47
          | (have j0 := b0e47 X0
             grind)
          | exact resolve b0e47 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e54 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b0e32 X0
             have i₂ := b0e33 X0
             grind)
          | (have i₁ := b0e32 x
             have i₂ := b0e33 x
             grind)
          | exact superpose b0e33 b0e32
          | exact resolve b0e32 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33
        have b0e145 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b0e13 (k (τ X0) X1)
             have i₂ := b0e35 X0 X1
             grind)
          | exact superpose b0e35 b0e13
          | exact resolve b0e13 b0e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e35
        have b0e212 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e29 X1 X2 X0
             have i₂ := b0e32 X0
             grind)
          | (have i₁ := b0e29 X0 X1 y
             have i₂ := b0e32 y
             grind)
          | exact superpose b0e32 b0e29
          | exact resolve b0e29 b0e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e29 b0e32
        have b0e265 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e212 X0 X1 x
             have i₂ := b0e41 X1 x
             grind)
          | exact superpose b0e41 b0e212
          | exact resolve b0e212 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e212
        have b0e679 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          grind
        have b0e684 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) x) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
          intro X0
          first
          | (have i₁ := b0e36 X0 (τ X0)
             have i₂ := b0e49 (τ X0)
             grind)
          | exact superpose b0e49 b0e36
          | (have j1 := b0e49 (τ X0)
             grind)
          | exact resolve b0e36 b0e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36 b0e49
        have b0e691 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) y) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
          intro X0
          first
          | (have i₁ := b0e684 X0
             have i₂ := b0e54 (σ (τ X0))
             grind)
          | exact superpose b0e54 b0e684
          | (have j0 := b0e684 X0
             grind)
          | exact resolve b0e684 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e684
        have b0e696 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) x) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e679 X0
             have i₂ := b0e54 (σ X0)
             grind)
          | exact superpose b0e54 b0e679
          | (have j0 := b0e679 X0
             grind)
          | exact resolve b0e679 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e679
        have b0e700 : ∀ X0 : G, (M.op X0 y) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
          intro X0
          first
          | (have i₁ := b0e691 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e691
          | (have j0 := b0e691 X0
             grind)
          | exact resolve b0e691 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e691
        have b0e705 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e696 X0
             have i₂ := b0e54 (σ X0)
             grind)
          | exact superpose b0e54 b0e696
          | (have j0 := b0e696 X0
             grind)
          | exact resolve b0e696 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e696
        have b0e706 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) y) ∨ (M.op X0 y) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b0e700 X0
             have i₂ := b0e54 (σ (τ X0))
             grind)
          | exact superpose b0e54 b0e700
          | (have j0 := b0e700 X0
             grind)
          | exact resolve b0e700 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e54 b0e700
        have b0e710 : ∀ X0 : G, (M.op X0 y) = (k X0 X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b0e706 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e706
          | (have j0 := b0e706 X0
             grind)
          | exact resolve b0e706 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e706
        have b0e995 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) y)) X0) := by
          intro X0
          first
          | (have i₁ := b0e145 (M.op (σ X0) y) X0
             have i₂ := b0e42 (σ X0)
             grind)
          | exact superpose b0e42 b0e145
          | exact resolve b0e145 b0e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42 b0e145
        have b0e1005 : ∀ X0 : G, (k (τ (M.op (σ X0) y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e995 X0
             have i₂ := b0e13 X0
             grind)
          | exact superpose b0e13 b0e995
          | exact resolve b0e995 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e995
        have b0e4997 : (σ x) = (M.op (σ x) y) ∨ (σ y) = (M.op (σ x) y) ∨ x = y := by
          first
          | (have i₁ := b0e705 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e705
          | (have j0 := b0e705 x
             grind)
          | exact resolve b0e705 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e705
        have b0e13934 : x = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) y) ∨ x = y := by
          first
          | (have i₁ := b0e1005 x
             have i₂ := b0e4997
             grind)
          | exact superpose b0e4997 b0e1005
          | exact resolve b0e1005 b0e4997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1005 b0e4997
        have b0e13964 : (σ y) = (M.op (σ x) y) ∨ x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b0e13934
             have i₂ := b0e13 x
             grind)
          | exact superpose b0e13 b0e13934
          | exact resolve b0e13934 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e13934
        have b0e14324 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b0e265 (σ x) X0
             have i₂ := b0e13964
             grind)
          | exact superpose b0e13964 b0e265
          | exact resolve b0e265 b0e13964
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e265
        have b0e22302 : (σ (M.op x y)) ≠ (M.op (σ x) y) ∨ x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e14324 (σ x)
             grind)
          | exact superpose b0e14324 b0e19
          | exact resolve b0e19 b0e14324
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e14324
        have b0e22323 : (σ y) ≠ (M.op (σ x) y) ∨ x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b0e22302
             have i₂ := b0e44
             grind)
          | exact superpose b0e44 b0e22302
          | exact resolve b0e22302 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e22302
        have b0e22328 : x = (k x x) ∨ x = y := by
          first
          | (have r₁ := b0e22323
             have r₂ := b0e13964
             grind)
          | exact resolve b0e22323 b0e13964
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e13964 b0e22323
        have b0e22992 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b0e710 x
             have i₂ := b0e22328
             grind)
          | exact superpose b0e22328 b0e710
          | (have j0 := b0e710 x
             grind)
          | exact resolve b0e710 b0e22328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e710 b0e22328
        have b0e23026 : x = (M.op x y) ∨ x = y := by grind
        clear b0e22992
        have b0e23045 : x = y ∨ x = y := by
          first
          | (have i₁ := b0e23026
             have i₂ := b0e44
             grind)
          | exact superpose b0e44 b0e23026
          | exact resolve b0e23026 b0e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e44 b0e23026
        have b0e23046 : x = y := by grind
        clear b0e23045
        have b0e23707 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e23046
             grind)
          | exact superpose b0e23046 b0e19
          | exact resolve b0e19 b0e23046
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23046
        have b0e23764 : (σ x) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e23707
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e23707
          | exact resolve b0e23707 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23707
        have b0e23765 : False := by grind
        exact b0e23765
      · rcases eq_or_ne (y) (x) with h2b | h2b
        · have b1e21 : x = (M.op y y) := by grind
          have b1e23 : y ≠ (M.op x x) := by grind
          have b1e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e31 : False := by grind
          exact b1e31
        · have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = (M.op y y) := by grind
          have b2e23 : y ≠ (M.op x x) := by grind
          have b2e24 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e31 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b2e13 X0 y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b2e45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b2e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e45 X0
               have i₂ := b2e31 (σ X0)
               grind)
            | exact superpose b2e31 b2e45
            | (have j0 := b2e45 X0
               grind)
            | exact resolve b2e45 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45
          have b2e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b2e46 X0
               have i₂ := b2e31 (σ X0)
               grind)
            | exact superpose b2e31 b2e46
            | (have j0 := b2e46 X0
               grind)
            | exact resolve b2e46 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46
          have b2e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b2e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 x) = X0 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e31 X1
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e31 X0
               have i₂ := b2e18 (M.op X0 X0) X1
               grind)
            | exact superpose b2e18 b2e31
            | (have j1 := b2e18 X0 X1
               grind)
            | exact resolve b2e31 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) x) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e60 X0 X1
               have i₂ := b2e31 (σ X0)
               grind)
            | exact superpose b2e31 b2e60
            | (have j0 := b2e60 X0 X1
               grind)
            | exact resolve b2e60 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31 b2e60
          have b2e543 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) x) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b2e36 X0 (τ X0)
               have i₂ := b2e48 (τ X0)
               grind)
            | exact superpose b2e48 b2e36
            | (have j1 := b2e48 (τ X0)
               grind)
            | exact resolve b2e36 b2e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36
          have b2e546 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) x)) ∨ (σ X0) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b2e14 (k X0 X0)
               have i₂ := b2e48 X0
               grind)
            | exact superpose b2e48 b2e14
            | (have j1 := b2e48 X0
               grind)
            | exact resolve b2e14 b2e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e48
          have b2e547 : ∀ X0 : G, (M.op X0 x) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b2e543 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e543
            | (have j0 := b2e543 X0
               grind)
            | exact resolve b2e543 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e543
          have b2e551 : ∀ X0 : G, (M.op X0 x) = (k X0 X0) ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b2e547 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e547
            | (have j0 := b2e547 X0
               grind)
            | exact resolve b2e547 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e547
          have b2e882 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e69 x y
               grind)
            | exact superpose b2e69 b2e20
            | (have j1 := b2e69 x y
               grind)
            | exact resolve b2e20 b2e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e69
          have b2e5907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b2e882
               have i₂ := b2e62 y x
               grind)
            | exact superpose b2e62 b2e882
            | (have j1 := b2e62 (σ y) (σ x)
               grind)
            | (have r₁ := b2e882
               have r₂ := b2e62 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b2e882
               have r₂ := b2e62 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b2e882 b2e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e62 b2e882
          have b2e5914 : (σ y) = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
          clear b2e5907
          have b2e5921 : (σ y) = (M.op (σ x) x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b2e5914
               have r₂ := b2e23
               grind)
            | exact resolve b2e5914 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5914
          have b2e5925 : (σ y) = (M.op (σ x) x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b2e5921
               have r₂ := b2e24
               grind)
            | exact resolve b2e5921 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5921
          have b2e5930 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e546 x
               have i₂ := b2e5925
               grind)
            | exact superpose b2e5925 b2e546
            | exact resolve b2e546 b2e5925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e546 b2e5925
          have b2e5944 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by grind
          clear b2e5930
          have b2e5950 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e5944
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e5944
            | exact resolve b2e5944 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5944
          have b2e6243 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e551 x
               have i₂ := b2e5950
               grind)
            | exact superpose b2e5950 b2e551
            | (have j0 := b2e551 x
               grind)
            | exact resolve b2e551 b2e5950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e551
          have b2e6251 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b2e6243
               have r₂ := b2e23
               grind)
            | exact resolve b2e6243 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6243
          have b2e6535 : x = (k x x) ∨ (σ x) = (σ y) := by grind
          clear b2e6251
          have b2e6945 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b2e5950
               have i₂ := b2e6535
               grind)
            | exact superpose b2e6535 b2e5950
            | exact resolve b2e5950 b2e6535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e5950 b2e6535
          have b2e6961 : x = y ∨ (σ x) = (σ y) := by grind
          clear b2e6945
          have b2e6965 : (σ x) = (σ y) := by
            first
            | (have r₁ := b2e6961
               have r₂ := b2e24
               grind)
            | exact resolve b2e6961 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6961
          have b2e7032 : x = (τ (σ y)) := by
            first
            | (have i₁ := b2e14 x
               have i₂ := b2e6965
               grind)
            | exact superpose b2e6965 b2e14
            | exact resolve b2e14 b2e6965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6965
          have b2e7088 : x = y := by
            first
            | (have i₁ := b2e7032
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e7032
            | exact resolve b2e7032 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e7032
          have b2e7096 : False := by grind
          exact b2e7096
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (σ x) = (σ y) := by grind
          have b3e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e27 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e29 : x = (τ (σ y)) := by
            first
            | (have i₁ := b3e14 x
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e14
            | exact resolve b3e14 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e30 : x = y := by
            first
            | (have i₁ := b3e29
               have i₂ := b3e14 y
               grind)
            | exact superpose b3e14 b3e29
            | exact resolve b3e29 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e29
          have b3e31 : y = (M.op y y) := by
            first
            | (have i₁ := b3e24
               have i₂ := b3e30
               grind)
            | exact superpose b3e30 b3e24
            | exact resolve b3e24 b3e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e30
          have b3e34 : y = (k y y) := by grind
          clear b3e31
          have b3e42 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b3e13 X0 x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e57 : (σ y) ≠ (M.op (σ y) y) := by
            first
            | (have i₁ := b3e27
               have i₂ := b3e42 (σ y)
               grind)
            | exact superpose b3e42 b3e27
            | exact resolve b3e27 b3e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e27
          have b3e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b3e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b3e71 X0
               have i₂ := b3e42 (σ X0)
               grind)
            | exact superpose b3e42 b3e71
            | (have j0 := b3e71 X0
               grind)
            | exact resolve b3e71 b3e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e71
          have b3e77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b3e75 X0
               have i₂ := b3e42 (σ X0)
               grind)
            | exact superpose b3e42 b3e75
            | (have j0 := b3e75 X0
               grind)
            | exact resolve b3e75 b3e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e42 b3e75
          have b3e533 : (σ y) = (M.op (σ y) y) ∨ (σ y) = (M.op (σ y) y) := by
            first
            | (have i₁ := b3e77 y
               have i₂ := b3e34
               grind)
            | exact superpose b3e34 b3e77
            | (have j0 := b3e77 y
               grind)
            | exact resolve b3e77 b3e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e34 b3e77
          have b3e542 : (σ y) = (M.op (σ y) y) := by grind
          clear b3e533
          have b3e547 : False := by grind
          exact b3e547
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b4e22 : x = (M.op y y) := by grind
            have b4e25 : y ≠ (M.op x x) := by grind
            have b4e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e34 : False := by grind
            exact b4e34
          · have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e24 : (σ x) = (σ y) := by grind
            have b5e26 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e31 : x = (τ (σ y)) := by
              first
              | (have i₁ := b5e15 x
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e15
              | exact resolve b5e15 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e32 : x = y := by
              first
              | (have i₁ := b5e31
                 have i₂ := b5e15 y
                 grind)
              | exact superpose b5e15 b5e31
              | exact resolve b5e31 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31
            have b5e33 : False := by grind
            exact b5e33
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b6e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : x = (M.op y y) := by grind
          have b6e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e23 : (σ x) ≠ (σ y) := by grind
          have b6e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e31 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b6e40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 (τ X0)
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e47 : ∀ X0 : G, (k (M.op X0 y) X0) = X0 := by
            intro X0
            grind
          have b6e48 : (σ x) ≠ (M.op (σ y) y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e31 (σ y)
               grind)
            | exact superpose b6e31 b6e22
            | exact resolve b6e22 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b6e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e51 X0
               have i₂ := b6e31 (σ X0)
               grind)
            | exact superpose b6e31 b6e51
            | (have j0 := b6e51 X0
               grind)
            | exact resolve b6e51 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e51
          have b6e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b6e52 X0
               have i₂ := b6e31 (σ X0)
               grind)
            | exact superpose b6e31 b6e52
            | (have j0 := b6e52 X0
               grind)
            | exact resolve b6e52 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e31 b6e52
          have b6e116 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b6e14 (k (τ X0) X1)
               have i₂ := b6e39 X0 X1
               grind)
            | exact superpose b6e39 b6e14
            | exact resolve b6e14 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39
          have b6e732 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = X0 := by
            intro X0
            grind
          have b6e737 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) y) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) y) := by
            intro X0
            first
            | (have i₁ := b6e40 X0 (τ X0)
               have i₂ := b6e54 (τ X0)
               grind)
            | exact superpose b6e54 b6e40
            | (have j1 := b6e54 (τ X0)
               grind)
            | exact resolve b6e40 b6e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e40 b6e54
          have b6e741 : ∀ X0 : G, (M.op X0 y) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) y) := by
            intro X0
            first
            | (have i₁ := b6e737 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e737
            | (have j0 := b6e737 X0
               grind)
            | exact resolve b6e737 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e737
          have b6e745 : ∀ X0 : G, (M.op X0 y) = (k X0 X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b6e741 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e741
            | (have j0 := b6e741 X0
               grind)
            | exact resolve b6e741 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e741
          have b6e1117 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) y)) X0) := by
            intro X0
            first
            | (have i₁ := b6e116 (M.op (σ X0) y) X0
               have i₂ := b6e47 (σ X0)
               grind)
            | exact superpose b6e47 b6e116
            | exact resolve b6e116 b6e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e47 b6e116
          have b6e1127 : ∀ X0 : G, (k (τ (M.op (σ X0) y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e1117 X0
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e1117
            | exact resolve b6e1117 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1117
          have b6e4224 : (σ x) = (M.op (σ y) y) ∨ (σ y) = (M.op (σ y) y) ∨ x = y := by
            first
            | (have i₁ := b6e732 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e732
            | (have j0 := b6e732 y
               grind)
            | exact resolve b6e732 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e732
          have b6e4251 : (σ y) = (M.op (σ y) y) ∨ x = y := by
            first
            | (have r₁ := b6e4224
               have r₂ := b6e48
               grind)
            | exact resolve b6e4224 b6e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e48 b6e4224
          have b6e4283 : y = (k (τ (σ y)) y) ∨ x = y := by
            first
            | (have i₁ := b6e1127 y
               have i₂ := b6e4251
               grind)
            | exact superpose b6e4251 b6e1127
            | exact resolve b6e1127 b6e4251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1127 b6e4251
          have b6e4301 : y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b6e4283
               have i₂ := b6e14 y
               grind)
            | exact superpose b6e14 b6e4283
            | exact resolve b6e4283 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e4283
          have b6e4461 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b6e745 y
               have i₂ := b6e4301
               grind)
            | exact superpose b6e4301 b6e745
            | (have j0 := b6e745 y
               grind)
            | exact resolve b6e745 b6e4301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e745 b6e4301
          have b6e4469 : y = (M.op y y) ∨ x = y := by grind
          clear b6e4461
          have b6e4479 : x = y ∨ x = y := by
            first
            | (have i₁ := b6e4469
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e4469
            | exact resolve b6e4469 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e4469
          have b6e4480 : x = y := by grind
          clear b6e4479
          have b6e4646 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e4480
               grind)
            | exact superpose b6e4480 b6e23
            | exact resolve b6e23 b6e4480
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e4480
          have b6e4663 : False := by grind
          exact b6e4663
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b7e24 : (σ x) ≠ (σ y) := by grind
            have b7e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e34 : False := by grind
            exact b7e34
          · have b8e14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
              intro X0 X1
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : x = (M.op y y) := by grind
            have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b8e26 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b8e14 X0 y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e37 : ∀ X0 : G, (k (M.op X0 x) X0) = X0 := by
              intro X0
              grind
            have b8e38 : (σ x) ≠ (M.op (σ y) x) := by
              first
              | (have i₁ := b8e23
                 have i₂ := b8e31 (σ y)
                 grind)
              | exact superpose b8e31 b8e23
              | exact resolve b8e23 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 (τ X0) X1
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b8e43 X0
                 have i₂ := b8e31 (σ X0)
                 grind)
              | exact superpose b8e31 b8e43
              | (have j0 := b8e43 X0
                 grind)
              | exact resolve b8e43 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e43
            have b8e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) x) ∨ (σ X0) = (M.op (σ X0) x) := by
              intro X0
              first
              | (have i₁ := b8e44 X0
                 have i₂ := b8e31 (σ X0)
                 grind)
              | exact superpose b8e31 b8e44
              | (have j0 := b8e44 X0
                 grind)
              | exact resolve b8e44 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31 b8e44
            have b8e102 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k (τ X0) X1)
                 have i₂ := b8e39 X0 X1
                 grind)
              | exact superpose b8e39 b8e15
              | exact resolve b8e15 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39
            have b8e429 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) x)) X0) := by
              intro X0
              first
              | (have i₁ := b8e102 (M.op (σ X0) x) X0
                 have i₂ := b8e37 (σ X0)
                 grind)
              | exact superpose b8e37 b8e102
              | exact resolve b8e102 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37 b8e102
            have b8e443 : ∀ X0 : G, (k (τ (M.op (σ X0) x)) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e429 X0
                 have i₂ := b8e15 X0
                 grind)
              | exact superpose b8e15 b8e429
              | exact resolve b8e429 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e429
            have b8e484 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) x) ∨ (M.op X0 X0) = X0 := by
              intro X0
              grind
            clear b8e46
            have b8e3032 : (σ x) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ y) x) ∨ x = y := by
              first
              | (have i₁ := b8e484 y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e484
              | (have j0 := b8e484 y
                 grind)
              | exact resolve b8e484 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e484
            have b8e3055 : (σ y) = (M.op (σ y) x) ∨ x = y := by
              first
              | (have r₁ := b8e3032
                 have r₂ := b8e38
                 grind)
              | exact resolve b8e3032 b8e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e38 b8e3032
            have b8e3063 : (σ y) = (M.op (σ y) x) := by
              first
              | (have r₁ := b8e3055
                 have r₂ := b8e26
                 grind)
              | exact resolve b8e3055 b8e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3055
            have b8e3073 : y = (k (τ (σ y)) y) := by
              first
              | (have i₁ := b8e443 y
                 have i₂ := b8e3063
                 grind)
              | exact superpose b8e3063 b8e443
              | exact resolve b8e443 b8e3063
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e443 b8e3063
            have b8e3091 : y = (k y y) := by
              first
              | (have i₁ := b8e3073
                 have i₂ := b8e15 y
                 grind)
              | exact superpose b8e15 b8e3073
              | exact resolve b8e3073 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3073
            have b8e3236 : y = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b8e3091
            have b8e3244 : y = (M.op y y) := by grind
            clear b8e3236
            have b8e3390 : x = y := by
              first
              | (have i₁ := b8e22
                 have i₂ := b8e3244
                 grind)
              | exact superpose b8e3244 b8e22
              | exact resolve b8e22 b8e3244
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e3244
            have b8e3405 : False := by grind
            exact b8e3405
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b9e21 : x ≠ (M.op y y) := by grind
          have b9e22 : x = y := by grind
          have b9e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e31 : False := by grind
          exact b9e31
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e23 : x = y := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b10e25 : y ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e35 : (σ y) = (k (σ y) (σ y)) := by grind
            have b10e36 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b10e35
                 have i₂ := b10e20 y y
                 grind)
              | exact superpose b10e20 b10e35
              | exact resolve b10e35 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e37 : (k y y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k y y)
                 have i₂ := b10e36
                 grind)
              | exact superpose b10e36 b10e15
              | exact resolve b10e15 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36
            have b10e38 : y = (k y y) := by
              first
              | (have i₁ := b10e37
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e37
              | exact resolve b10e37 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e37
            have b10e56 : y = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b10e38
            have b10e58 : y = (M.op y y) := by grind
            clear b10e56
            have b10e61 : False := by grind
            exact b10e61
          · have b11e23 : x = y := by grind
            have b11e26 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e34 : False := by grind
            exact b11e34
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b12e22 : x ≠ (M.op y y) := by grind
            have b12e23 : x = y := by grind
            have b12e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e34 : False := by grind
            exact b12e34
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = y := by grind
              have b13e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b13e27 : y ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b13e402 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e46
              have b13e424 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
              clear b13e402
              have b13e427 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
              clear b13e424
              have b13e428 : y = (M.op y y) := by grind
              clear b13e427
              have b13e429 : False := by grind
              exact b13e429
            · have b14e24 : x = y := by grind
              have b14e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e37 : False := by grind
              exact b14e37
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b15e23 : x = y := by grind
            have b15e25 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e34 : False := by grind
            exact b15e34
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b16e24 : x = y := by grind
              have b16e26 : (σ x) ≠ (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e37 : False := by grind
              exact b16e37
            · have b17e24 : x = y := by grind
              have b17e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e37 : False := by grind
              exact b17e37
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op y y) := by grind
          have b18e22 : x ≠ y := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ y)) := by grind
          have b18e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e33 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e49 : (σ x) = (M.op (σ y) y) := by
            first
            | (have i₁ := b18e23
               have i₂ := b18e33 (σ y)
               grind)
            | exact superpose b18e33 b18e23
            | exact resolve b18e23 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b18e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b18e52 X0
               have i₂ := b18e33 (σ X0)
               grind)
            | exact superpose b18e33 b18e52
            | (have j0 := b18e52 X0
               grind)
            | exact resolve b18e52 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e52
          have b18e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b18e53 X0
               have i₂ := b18e33 (σ X0)
               grind)
            | exact superpose b18e33 b18e53
            | (have j0 := b18e53 X0
               grind)
            | exact resolve b18e53 b18e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e33 b18e53
          have b18e564 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) y)) ∨ (σ X0) = (M.op (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b18e14 (k X0 X0)
               have i₂ := b18e55 X0
               grind)
            | exact superpose b18e55 b18e14
            | (have j1 := b18e55 X0
               grind)
            | exact resolve b18e14 b18e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1913 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e564 y
               have i₂ := b18e49
               grind)
            | exact superpose b18e49 b18e564
            | exact resolve b18e564 b18e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e564
          have b18e1953 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e1913
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e1913
            | exact resolve b18e1913 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1913
          have b18e1973 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b18e1953
          have b18e1974 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b18e1973
               have r₂ := b18e21
               grind)
            | exact resolve b18e1973 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1973
          have b18e2097 : y = (k y y) ∨ (σ x) = (σ y) := by grind
          clear b18e1974
          have b18e2255 : (σ y) = (M.op (σ y) y) ∨ (σ y) = (M.op (σ y) y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e55 y
               have i₂ := b18e2097
               grind)
            | exact superpose b18e2097 b18e55
            | (have j0 := b18e55 y
               grind)
            | exact resolve b18e55 b18e2097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e55 b18e2097
          have b18e2258 : (σ y) = (M.op (σ y) y) ∨ (σ x) = (σ y) := by grind
          clear b18e2255
          have b18e2264 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e2258
               have i₂ := b18e49
               grind)
            | exact superpose b18e49 b18e2258
            | exact resolve b18e2258 b18e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e49 b18e2258
          have b18e2265 : (σ x) = (σ y) := by grind
          clear b18e2264
          have b18e2459 : x = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 x
               have i₂ := b18e2265
               grind)
            | exact superpose b18e2265 b18e14
            | exact resolve b18e14 b18e2265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e2265
          have b18e2493 : x = y := by
            first
            | (have i₁ := b18e2459
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e2459
            | exact resolve b18e2459 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e2459
          have b18e2499 : False := by grind
          exact b18e2499
        · rcases eq_or_ne (y) (x) with h2b | h2b
          · have b19e23 : x ≠ y := by grind
            have b19e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e34 : False := by grind
            exact b19e34
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : x ≠ (M.op y y) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b20e26 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b20e619 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e48 y
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e48
              | exact resolve b20e48 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e48
            have b20e1039 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e15 (k y y)
                 have i₂ := b20e619
                 grind)
              | exact superpose b20e619 b20e15
              | exact resolve b20e15 b20e619
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1054 : x = (k y y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e1039
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e1039
              | exact resolve b20e1039 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1039
            have b20e1074 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
            clear b20e1054
            have b20e1075 : y = (M.op y y) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b20e1074
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e1074 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1074
            have b20e1151 : y = (k y y) ∨ (σ x) = (σ y) := by grind
            clear b20e1075
            have b20e1234 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e619
                 have i₂ := b20e1151
                 grind)
              | exact superpose b20e1151 b20e619
              | exact resolve b20e619 b20e1151
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e619 b20e1151
            have b20e1237 : (σ x) = (σ y) := by grind
            clear b20e1234
            have b20e1313 : x = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 x
                 have i₂ := b20e1237
                 grind)
              | exact superpose b20e1237 b20e15
              | exact resolve b20e15 b20e1237
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1237
            have b20e1345 : x = y := by
              first
              | (have i₁ := b20e1313
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e1313
              | exact resolve b20e1313 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1313
            have b20e1355 : False := by grind
            exact b20e1355
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e23 : x ≠ y := by grind
            have b21e25 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : x = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 x
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e15
              | exact resolve b21e15 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e32 : x = y := by
              first
              | (have i₁ := b21e31
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e31
              | exact resolve b21e31 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31
            have b21e33 : False := by grind
            exact b21e33
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b22e24 : x ≠ y := by grind
              have b22e28 : x = y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e37 : False := by grind
              exact b22e37
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e26 : (σ x) = (σ y) := by grind
              have b23e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e33 : x = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 x
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e16
                | exact resolve b23e16 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e34 : x = y := by
                first
                | (have i₁ := b23e33
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e33
                | exact resolve b23e33 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e33
              have b23e35 : False := by grind
              exact b23e35
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
              intro X0 X1
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e23 : x ≠ y := by grind
            have b24e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e31 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b24e14 X0 x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e36 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 y)) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 X0
                 have i₂ := b24e31 X0
                 grind)
              | (have i₁ := b24e14 X0 y
                 have i₂ := b24e31 y
                 grind)
              | exact superpose b24e31 b24e14
              | exact resolve b24e14 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e38 : ∀ X0 : G, (k (M.op X0 y) X0) = X0 := by
              intro X0
              grind
            have b24e40 : y = (M.op x y) := by
              first
              | (have i₁ := b24e26
                 have i₂ := b24e31 x
                 grind)
              | exact superpose b24e31 b24e26
              | exact resolve b24e26 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e41 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b24e42 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
            have b24e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b24e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b24e46 X0
                 have i₂ := b24e31 (σ X0)
                 grind)
              | exact superpose b24e31 b24e46
              | (have j0 := b24e46 X0
                 grind)
              | exact resolve b24e46 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e46
            have b24e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) y) := by
              intro X0
              first
              | (have i₁ := b24e47 X0
                 have i₂ := b24e31 (σ X0)
                 grind)
              | exact superpose b24e31 b24e47
              | (have j0 := b24e47 X0
                 grind)
              | exact resolve b24e47 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e47
            have b24e86 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e15 (k (τ X0) X1)
                 have i₂ := b24e41 X0 X1
                 grind)
              | exact superpose b24e41 b24e15
              | exact resolve b24e15 b24e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e41
            have b24e100 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
              intro X0 X1
              first
              | (have i₁ := b24e31 X0
                 have i₂ := b24e36 X1 X0
                 grind)
              | (have i₁ := b24e31 (M.op X0 y)
                 have i₂ := b24e36 X0 (M.op X0 y)
                 grind)
              | exact superpose b24e36 b24e31
              | exact resolve b24e31 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e36
            have b24e450 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) y)) X0) := by
              intro X0
              first
              | (have i₁ := b24e86 (M.op (σ X0) y) X0
                 have i₂ := b24e38 (σ X0)
                 grind)
              | exact superpose b24e38 b24e86
              | exact resolve b24e86 b24e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e38 b24e86
            have b24e464 : ∀ X0 : G, (k (τ (M.op (σ X0) y)) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e450 X0
                 have i₂ := b24e15 X0
                 grind)
              | exact superpose b24e15 b24e450
              | exact resolve b24e450 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e450
            have b24e475 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) y) ∨ (M.op X0 X0) = X0 := by
              intro X0
              grind
            have b24e480 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) y) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) y) := by
              intro X0
              first
              | (have i₁ := b24e42 X0 (τ X0)
                 have i₂ := b24e49 (τ X0)
                 grind)
              | exact superpose b24e49 b24e42
              | (have j1 := b24e49 (τ X0)
                 grind)
              | exact resolve b24e42 b24e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42 b24e49
            have b24e485 : ∀ X0 : G, (M.op X0 y) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) y) := by
              intro X0
              first
              | (have i₁ := b24e480 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e480
              | (have j0 := b24e480 X0
                 grind)
              | exact resolve b24e480 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e480
            have b24e489 : ∀ X0 : G, (M.op X0 y) = (k X0 X0) ∨ (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b24e485 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e485
              | (have j0 := b24e485 X0
                 grind)
              | exact resolve b24e485 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e485
            have b24e3191 : (σ y) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = y := by
              first
              | (have i₁ := b24e475 x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e475
              | (have j0 := b24e475 x
                 grind)
              | exact resolve b24e475 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e475
            have b24e3235 : (σ x) = (M.op (σ x) y) ∨ (σ y) = (M.op (σ x) y) := by
              first
              | (have r₁ := b24e3191
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e3191 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3191
            have b24e3243 : x = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) y) := by
              first
              | (have i₁ := b24e464 x
                 have i₂ := b24e3235
                 grind)
              | exact superpose b24e3235 b24e464
              | exact resolve b24e464 b24e3235
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e464 b24e3235
            have b24e3259 : (σ y) = (M.op (σ x) y) ∨ x = (k x x) := by
              first
              | (have i₁ := b24e3243
                 have i₂ := b24e15 x
                 grind)
              | exact superpose b24e15 b24e3243
              | exact resolve b24e3243 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3243
            have b24e3409 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) ∨ x = (k x x) := by
              intro X0
              first
              | (have i₁ := b24e100 X0 (σ x)
                 have i₂ := b24e3259
                 grind)
              | exact superpose b24e3259 b24e100
              | exact resolve b24e100 b24e3259
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e100
            have b24e4141 : (σ (M.op x y)) ≠ (M.op (σ x) y) ∨ x = (k x x) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e3409 (σ x)
                 grind)
              | exact superpose b24e3409 b24e21
              | exact resolve b24e21 b24e3409
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3409
            have b24e4150 : (σ y) ≠ (M.op (σ x) y) ∨ x = (k x x) := by
              first
              | (have i₁ := b24e4141
                 have i₂ := b24e40
                 grind)
              | exact superpose b24e40 b24e4141
              | exact resolve b24e4141 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4141
            have b24e4155 : x = (k x x) := by
              first
              | (have r₁ := b24e4150
                 have r₂ := b24e3259
                 grind)
              | exact resolve b24e4150 b24e3259
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3259 b24e4150
            have b24e4185 : x = (M.op x y) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b24e489 x
                 have i₂ := b24e4155
                 grind)
              | exact superpose b24e4155 b24e489
              | (have j0 := b24e489 x
                 grind)
              | exact resolve b24e489 b24e4155
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e489 b24e4155
            have b24e4192 : x = (M.op x y) := by grind
            clear b24e4185
            have b24e4199 : x = y := by
              first
              | (have i₁ := b24e4192
                 have i₂ := b24e40
                 grind)
              | exact superpose b24e40 b24e4192
              | exact resolve b24e4192 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e40 b24e4192
            have b24e4204 : False := by grind
            exact b24e4204
          · rcases eq_or_ne (y) (x) with h2b | h2b
            · have b25e26 : (σ x) ≠ (σ y) := by grind
              have b25e28 : x = y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e37 : False := by grind
              exact b25e37
            · have b26e15 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
                intro X0 X1
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (σ y) := by grind
              have b26e27 : y ≠ (M.op x x) := by grind
              have b26e28 : x ≠ y := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e32 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X2 X0
                   have i₂ := b26e15 X0 X1
                   grind)
                | (have i₁ := b26e15 X0 (M.op X1 X1)
                   have i₂ := b26e15 (M.op X1 X1) X1
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e33 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) X0) = X0 := by
                intro X0 X1
                grind
              have b26e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b26e35 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b26e42 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e34 X0 X1
                   grind)
                | exact superpose b26e34 b26e16
                | exact resolve b26e16 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b26e49 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (M.op X1 X1))) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e35 X0 (M.op (τ X0) (M.op X1 X1))
                   have i₂ := b26e33 (τ X0) X1
                   grind)
                | exact superpose b26e33 b26e35
                | exact resolve b26e35 b26e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33 b26e35
              have b26e59 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (M.op X1 X1))) X0) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e49 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e49
                | exact resolve b26e49 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49
              have b26e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
              have b26e76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e42 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e42
                | exact resolve b26e42 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e391 : ∀ X0 X1 X2 X3 : G, (k (σ (M.op (τ X3) (M.op X0 (M.op X1 (M.op X2 X2))))) X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e59 X3 X0
                   have i₂ := b26e32 X1 X2 X0
                   grind)
                | (have i₁ := b26e59 X0 (M.op X0 (M.op X1 X1))
                   have i₂ := b26e32 X0 X1 (M.op X0 (M.op X1 X1))
                   grind)
                | exact superpose b26e32 b26e59
                | exact resolve b26e59 b26e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e32 b26e59
              have b26e437 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e44 X0
                   have i₂ := b26e15 (σ X0) X1
                   grind)
                | exact superpose b26e15 b26e44
                | exact resolve b26e44 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e703 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e44 X0
                   have i₂ := b26e67 X0 X1
                   grind)
                | exact superpose b26e67 b26e44
                | (have j1 := b26e67 X1 X0
                   grind)
                | exact resolve b26e44 b26e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44 b26e67
              have b26e725 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have j0 := b26e703 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e703
              have b26e6370 : ∀ X0 X1 : G, (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (M.op X1 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e34 X0 (τ X0)
                   have i₂ := b26e437 (τ X0) X1
                   grind)
                | exact superpose b26e437 b26e34
                | (have j1 := b26e437 (τ X0) X1
                   grind)
                | exact resolve b26e34 b26e437
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e437
              have b26e6481 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X1 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e6370 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e6370
                | (have j0 := b26e6370 X0 X1
                   grind)
                | exact resolve b26e6370 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6370
              have b26e6490 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 X0) ∨ (M.op X0 (M.op X1 X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e6481 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e6481
                | (have j0 := b26e6481 X0 X1
                   grind)
                | exact resolve b26e6481 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6481
              have b26e11029 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (M.op X1 X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X0 X1
                   have i₂ := b26e6490 X0 X1
                   grind)
                | exact superpose b26e6490 b26e15
                | (have j1 := b26e6490 X0 X1
                   grind)
                | exact resolve b26e15 b26e6490
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e6490
              have b26e11920 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b26e391 (M.op x (M.op x x)) x x X0
                   have i₂ := b26e11029 (τ X0) (M.op x (M.op x x))
                   grind)
                | exact superpose b26e11029 b26e391
                | (have j1 := b26e11029 (τ X0) x
                   grind)
                | exact resolve b26e391 b26e11029
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e391 b26e11029
              have b26e11943 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b26e11920 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e11920
                | (have j0 := b26e11920 X0
                   grind)
                | exact resolve b26e11920 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11920
              have b26e11977 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e11943 X0
                   have i₂ := b26e76 X0 X0
                   grind)
                | exact superpose b26e76 b26e11943
                | (have j0 := b26e11943 X0
                   grind)
                | exact resolve b26e11943 b26e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e76 b26e11943
              have b26e13505 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e725 y x
                   grind)
                | exact superpose b26e725 b26e22
                | (have j1 := b26e725 y x
                   grind)
                | exact resolve b26e22 b26e725
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e725
              have b26e13704 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) := by
                first
                | (have r₁ := b26e13505
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e13505 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e13505
              have b26e21706 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e11977 (σ X0)
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e11977
                | (have j0 := b26e11977 (σ X0)
                   grind)
                | exact resolve b26e11977 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e11977
              have b26e21844 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21706 X0
                   have i₂ := b26e42 (σ X0) X0
                   grind)
                | exact superpose b26e42 b26e21706
                | (have j0 := b26e21706 X0
                   grind)
                | exact resolve b26e21706 b26e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e42 b26e21706
              have b26e21848 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21844 X0
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e21844
                | (have j0 := b26e21844 X0
                   grind)
                | exact resolve b26e21844 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e21844
              have b26e21850 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have i₁ := b26e21848 X0
                   have i₂ := b26e21 X0 X0
                   grind)
                | exact superpose b26e21 b26e21848
                | (have j0 := b26e21848 X0
                   grind)
                | exact resolve b26e21848 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e21848
              have b26e44232 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b26e13704
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e13704
                | (have j1 := b26e20 y x
                   grind)
                | (have r₁ := b26e13704
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b26e13704
                   have r₂ := b26e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b26e13704 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e13704
              have b26e44253 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ x = y := by grind
              clear b26e44232
              have b26e44265 : (σ y) = (σ (k x x)) ∨ x = y := by
                first
                | (have r₁ := b26e44253
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e44253 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44253
              have b26e44267 : (σ y) = (σ (k x x)) := by
                first
                | (have r₁ := b26e44265
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e44265 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44265
              have b26e46352 : (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by
                first
                | (have i₁ := b26e21850 x
                   have i₂ := b26e44267
                   grind)
                | exact superpose b26e44267 b26e21850
                | (have j0 := b26e21850 x
                   grind)
                | exact resolve b26e21850 b26e44267
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e21850
              have b26e46355 : (k x x) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (k x x)
                   have i₂ := b26e44267
                   grind)
                | exact superpose b26e44267 b26e16
                | exact resolve b26e16 b26e44267
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44267
              have b26e46495 : y = (k x x) := by
                first
                | (have i₁ := b26e46355
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e46355
                | exact resolve b26e46355 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e46355
              have b26e46496 : (M.op x x) = (k x x) := by
                first
                | (have r₁ := b26e46352
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e46352 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e46352
              have b26e46502 : y = (M.op x x) := by
                first
                | (have i₁ := b26e46496
                   have i₂ := b26e46495
                   grind)
                | exact superpose b26e46495 b26e46496
                | exact resolve b26e46496 b26e46495
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e46495 b26e46496
              have b26e46506 : False := by grind
              exact b26e46506

/-- `Equation311`: `x ◇ x = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e54
        | exact resolve b0e54 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e54
      have b0e310 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e59 y
           grind)
        | exact superpose b0e59 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e59 y
           grind)
        | exact resolve b0e22 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e59
      have b0e324 : False := by grind
      exact b0e324
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y y) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
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
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e54
        have b1e60 : (M.op x x) = (k x y) := by grind
        clear b1e51
        have b1e61 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e62 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e57 x
             grind)
          | exact superpose b1e57 b1e61
          | exact resolve b1e61 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b1e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e64 X0
             have i₂ := b1e57 X0
             grind)
          | exact superpose b1e57 b1e64
          | exact resolve b1e64 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e64
        have b1e78 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e82 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e78 X0
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e78
          | (have j0 := b1e78 X0
             grind)
          | exact resolve b1e78 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e173 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e23
          | exact resolve b1e23 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e2369 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e82 (σ y)
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e82
          | (have j0 := b1e82 (σ y)
             grind)
          | (have r₁ := b1e82 (σ y)
             have r₂ := b1e62
             grind)
          | exact resolve b1e82 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e82
        have b1e2387 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e2369
        have b1e2397 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e2387
             have i₂ := b1e71 y
             grind)
          | exact superpose b1e71 b1e2387
          | exact resolve b1e2387 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2387
        have b1e2409 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e2397
             have r₂ := b1e173
             grind)
          | exact resolve b1e2397 b1e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2397
        have b1e2417 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e2409
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e2409
          | exact resolve b1e2409 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2409
        have b1e2425 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e2417
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e2417
          | exact resolve b1e2417 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e2417
        have b1e2432 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e2425
             have i₂ := b1e71 y
             grind)
          | exact superpose b1e71 b1e2425
          | exact resolve b1e2425 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71 b1e2425
        have b1e2438 : False := by grind
        exact b1e2438
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 y y
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
        have b2e56 : (M.op x x) = (k x y) := by grind
        clear b2e50
        have b2e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b2e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e58 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e58
          | exact resolve b2e58 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e58
        have b2e97 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
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
        have b2e288 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e65 x
             grind)
          | exact superpose b2e65 b2e22
          | exact resolve b2e22 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e2153 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e97 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e97
        have b2e2154 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2153
             have r₂ := b2e21
             grind)
          | exact resolve b2e2153 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2153
        have b2e2161 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2154
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2154
          | exact resolve b2e2154 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2154
        have b2e2168 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2161
             have i₂ := b2e56
             grind)
          | exact superpose b2e56 b2e2161
          | exact resolve b2e2161 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e2161
        have b2e2169 : False := by grind
        exact b2e2169
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e38
        have b3e45 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b3e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e41 (σ X0)
             grind)
          | exact superpose b3e41 b3e18
          | exact resolve b3e18 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e48 X0
             have i₂ := b3e41 X0
             grind)
          | exact superpose b3e41 b3e48
          | exact resolve b3e48 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e54 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e152 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e15
          | exact resolve b3e15 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e154 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e152
        have b3e155 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e154
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e154
          | exact resolve b3e154 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154
        have b3e156 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e41 x
             grind)
          | exact superpose b3e41 b3e155
          | exact resolve b3e155 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e155
        have b3e157 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e156
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e156
          | exact resolve b3e156 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e309 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e51 y
             grind)
          | exact superpose b3e51 b3e23
          | exact resolve b3e23 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e51
        have b3e373 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e54 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e374 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e373
             have r₂ := b3e20
             grind)
          | exact resolve b3e373 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e373
        have b3e381 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e157
             have i₂ := b3e374
             grind)
          | exact superpose b3e374 b3e157
          | exact resolve b3e157 b3e374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157 b3e374
        have b3e385 : False := by grind
        exact b3e385
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e51 (σ X0)
               grind)
            | exact superpose b4e51 b4e19
            | exact resolve b4e19 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e54 X0
               have i₂ := b4e51 X0
               grind)
            | exact superpose b4e51 b4e54
            | exact resolve b4e54 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e54
          have b4e332 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e59 x
               grind)
            | exact superpose b4e59 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e59 x
               grind)
            | exact resolve b4e28 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e59
          have b4e349 : False := by grind
          exact b4e349
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e48 (σ X0)
               grind)
            | exact superpose b5e48 b5e19
            | exact resolve b5e19 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e51 X0
               have i₂ := b5e48 X0
               grind)
            | exact superpose b5e48 b5e51
            | exact resolve b5e51 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e51
          have b5e61 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e61
          have b5e66 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e65
               have r₂ := b5e25
               grind)
            | exact resolve b5e65 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e65
          have b5e83 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e315 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e56 y
               grind)
            | exact superpose b5e56 b5e23
            | exact resolve b5e23 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e1886 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e83 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e1887 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1886
               have r₂ := b5e24
               grind)
            | exact resolve b5e1886 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1886
          have b5e1889 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1887
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1887
            | exact resolve b5e1887 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1887
          have b5e1891 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1889
               have i₂ := b5e66
               grind)
            | exact superpose b5e66 b5e1889
            | exact resolve b5e1889 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e1889
          have b5e1892 : False := by grind
          exact b5e1892
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e36 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ y) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e36
        have b6e41 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e145 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e15
          | exact resolve b6e15 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e147 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e145
        have b6e148 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e147
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e147
          | exact resolve b6e147 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e147
        have b6e149 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e148
             have i₂ := b6e38 x
             grind)
          | exact superpose b6e38 b6e148
          | exact resolve b6e148 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e148
        have b6e153 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e149
             grind)
          | exact superpose b6e149 b6e13
          | exact resolve b6e13 b6e149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e154 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e153
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e153
          | exact resolve b6e153 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e234 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e154
             grind)
          | exact superpose b6e154 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e154
        have b6e235 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e234
        have b6e237 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e235
             have r₂ := b6e21
             grind)
          | exact resolve b6e235 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e235
        have b6e239 : False := by grind
        exact b6e239
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e48 (σ X0)
               grind)
            | exact superpose b7e48 b7e19
            | exact resolve b7e19 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e51 X0
               have i₂ := b7e48 X0
               grind)
            | exact superpose b7e48 b7e51
            | exact resolve b7e51 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e51
          have b7e62 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e62
          have b7e66 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e25
               grind)
            | exact resolve b7e64 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e64
          have b7e67 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
          have b7e68 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e56 y
               grind)
            | exact superpose b7e56 b7e67
            | exact resolve b7e67 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e67
          have b7e150 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e14
            | exact resolve b7e14 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e151 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e150
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e150
            | exact resolve b7e150 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e225 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e151
               grind)
            | exact superpose b7e151 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e226 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e225
          have b7e228 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e226
               have r₂ := b7e21
               grind)
            | exact resolve b7e226 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226
          have b7e230 : False := by grind
          exact b7e230
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e104 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ y) (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1990 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e104 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e1991 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1990
               have r₂ := b8e24
               grind)
            | exact resolve b8e1990 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1990
          have b8e1993 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1991
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1991
            | exact resolve b8e1991 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1991
          have b8e1998 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1993
               grind)
            | exact superpose b8e1993 b8e20
            | exact resolve b8e20 b8e1993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1993
          have b8e2050 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e1998
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1998
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1998 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1998
          have b8e2054 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e2050
          have b8e2057 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e2054
               have r₂ := b8e21
               grind)
            | exact resolve b8e2054 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2054
          have b8e2058 : False := by grind
          exact b8e2058

/-- `Equation314`: `x ◇ x = y ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_x_y_pxy_Equation314 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law314 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law314.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e11 y x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e23 X0
           grind)
        | exact superpose b0e23 b0e11
        | exact resolve b0e11 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e36 X0 x
           have i₂ := b0e23 x
           grind)
        | exact superpose b0e23 b0e36
        | exact resolve b0e36 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e44 : y = (σ y) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e38 (σ y)
           grind)
        | exact superpose b0e38 b0e20
        | exact resolve b0e20 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e69 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e18
        | exact resolve b0e18 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e69
           have i₂ := b0e23 (σ x)
           grind)
        | exact superpose b0e23 b0e69
        | exact resolve b0e69 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e76 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e75
           have i₂ := b0e23 x
           grind)
        | exact superpose b0e23 b0e75
        | exact resolve b0e75 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e75
      have b0e77 : False := by grind
      exact b0e77
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 y x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e34 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e31 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 y
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b1e36 X0 x
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e36
          | exact resolve b1e36 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e36
        have b1e39 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e44 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e38 (σ y)
             grind)
          | exact superpose b1e38 b1e21
          | exact resolve b1e21 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ y) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e59
        have b1e65 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e61
             have r₂ := b1e21
             grind)
          | exact resolve b1e61 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e71 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e65
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e65
          | exact resolve b1e65 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e75 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e71
             have i₂ := b1e34 x
             grind)
          | exact superpose b1e34 b1e71
          | exact resolve b1e71 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e90 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X0 X1) = X1 ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X1 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X2 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e97 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 X0
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e16 X1 X1
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X0 X0
             have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e100 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e17 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e101 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e97 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97
        have b1e102 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e101 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e104 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ y = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e100 X0 X1
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e100
          | (have j0 := b1e100 X0 X1
             grind)
          | (have r₁ := b1e100 y y
             have r₂ := b1e38 y
             grind)
          | exact resolve b1e100 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100
        have b1e106 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 ∨ y = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e102 X0 X1
             have i₂ := b1e38 X0
             grind)
          | exact superpose b1e38 b1e102
          | (have j0 := b1e102 X0 X1
             grind)
          | exact resolve b1e102 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102
        have b1e111 : ∀ X0 X1 X2 : G, y = X1 ∨ (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X0 X1) = X1 ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e90 X0 X1 X2
             have i₂ := b1e38 X1
             grind)
          | exact superpose b1e38 b1e90
          | (have j0 := b1e90 X0 X1 X2
             grind)
          | exact resolve b1e90 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e120 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ y = X1 ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e111 X0 X1 X2
             have j1 := b1e104 X1 X0
             grind)
          | (have r₁ := b1e111 X0 (M.op X1 y) X2
             have r₂ := b1e104 y X1
             grind)
          | (have r₁ := b1e111 X1 X0 X2
             have r₂ := b1e104 X0 X1
             grind)
          | exact resolve b1e111 b1e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e104 b1e111
        have b1e201 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e39 X0 y
             have i₂ := b1e34 (τ X0)
             grind)
          | exact superpose b1e34 b1e39
          | exact resolve b1e39 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e209 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e201 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e201
          | exact resolve b1e201 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e201
        have b1e885 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e106 (σ y) X0
             have i₂ := b1e209 X0
             grind)
          | exact superpose b1e209 b1e106
          | (have j0 := b1e106 (σ y) x
             grind)
          | exact resolve b1e106 b1e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e911 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b1e885 X0
             grind)
          | (have r₁ := b1e885 y
             have r₂ := b1e44
             grind)
          | (have r₁ := b1e885 X0
             have r₂ := b1e44
             grind)
          | exact resolve b1e885 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e885
        have b1e1104 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (σ y)) ∨ y = (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e120 (σ x) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e120
          | (have j0 := b1e120 (σ y) (σ y) X0
             grind)
          | (have r₁ := b1e120 (σ x) (σ y) (σ y)
             have r₂ := b1e22
             grind)
          | (have r₁ := b1e120 (σ y) (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e120 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120
        have b1e1132 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b1e1104 X0
             grind)
          | (have r₁ := b1e1104 X0
             have r₂ := b1e44
             grind)
          | exact resolve b1e1104 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1104
        have b1e1139 : ∀ X0 : G, y ≠ (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1132 X0
             have i₂ := b1e38 (σ y)
             grind)
          | exact superpose b1e38 b1e1132
          | (have j0 := b1e1132 X0
             grind)
          | exact resolve b1e1132 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1132
        have b1e1141 : ∀ X0 : G, (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1139 X0
             have i₂ := b1e209 X0
             grind)
          | exact superpose b1e209 b1e1139
          | (have j0 := b1e1139 X0
             grind)
          | exact resolve b1e1139 b1e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e209 b1e1139
        have b1e1143 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1141 X0
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e1141
          | (have j0 := b1e1141 X0
             grind)
          | exact resolve b1e1141 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1141
        have b1e1144 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1143 X0
             have i₂ := b1e34 x
             grind)
          | exact superpose b1e34 b1e1143
          | (have j0 := b1e1143 X0
             grind)
          | exact resolve b1e1143 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e1143
        have b1e1145 : ∀ X0 : G, y = (σ x) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1144 X0
             have i₂ := b1e38 (σ y)
             grind)
          | exact superpose b1e38 b1e1144
          | (have j0 := b1e1144 X0
             grind)
          | (have r₁ := b1e1144 (σ y)
             have r₂ := b1e38 (σ y)
             grind)
          | exact resolve b1e1144 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e1144
        have b1e1146 : ∀ X0 : G, y = (σ y) ∨ (σ y) = X0 ∨ y ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e1145 X0
             have i₂ := b1e75
             grind)
          | exact superpose b1e75 b1e1145
          | (have j0 := b1e1145 X0
             grind)
          | exact resolve b1e1145 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75 b1e1145
        have b1e1147 : ∀ X0 : G, y ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b1e1146 X0
             grind)
          | (have r₁ := b1e1146 X0
             have r₂ := b1e44
             grind)
          | (have r₁ := b1e1146 y
             have r₂ := b1e44
             grind)
          | exact resolve b1e1146 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1146
        have b1e1445 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1147 X0
             have i₂ := b1e911 X0
             grind)
          | exact superpose b1e911 b1e1147
          | (have j0 := b1e1147 X0
             have j1 := b1e911 X0
             grind)
          | (have r₁ := b1e1147 y
             have r₂ := b1e911 y
             grind)
          | exact resolve b1e1147 b1e911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e911 b1e1147
        have b1e1467 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b1e1445 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1445
        have b1e1522 : y = (σ y) := by
          first
          | (have j0 := b1e1467 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1467
        have b1e1523 : False := by grind
        exact b1e1523
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e12 y x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b2e33 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e30 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e35 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 y
             have i₂ := b2e25 X0
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b2e35 X0 x
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e35
          | exact resolve b2e35 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e35
        have b2e38 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e42 : y ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e37 (σ y)
             grind)
          | exact superpose b2e37 b2e21
          | exact resolve b2e21 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e16 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X0 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e86 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e91 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e90 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e95 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 ∨ y = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e91 X0 X1
             have i₂ := b2e37 X0
             grind)
          | exact superpose b2e37 b2e91
          | (have j0 := b2e91 X0 X1
             grind)
          | exact resolve b2e91 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e174 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e38 X0 y
             have i₂ := b2e33 (τ X0)
             grind)
          | exact superpose b2e33 b2e38
          | exact resolve b2e38 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e38
        have b2e182 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e174 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e174
          | exact resolve b2e174 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174
        have b2e839 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e95 (σ y) X0
             have i₂ := b2e182 X0
             grind)
          | exact superpose b2e182 b2e95
          | (have j0 := b2e95 (σ y) x
             grind)
          | exact resolve b2e95 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e865 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e839 X0
             grind)
          | (have r₁ := b2e839 y
             have r₂ := b2e42
             grind)
          | (have r₁ := b2e839 X0
             have r₂ := b2e42
             grind)
          | exact resolve b2e839 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e839
        have b2e1083 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e16 X0 (σ y)
             have i₂ := b2e865 X0
             grind)
          | exact superpose b2e865 b2e16
          | (have j0 := b2e16 X0 (σ y)
             have j1 := b2e865 (σ y)
             grind)
          | (have r₁ := b2e16 (M.op (σ y) (σ y)) (σ y)
             have r₂ := b2e865 (M.op (σ y) (σ y))
             grind)
          | exact resolve b2e16 b2e865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e865
        have b2e1109 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e1083 X0
             grind)
          | (have r₁ := b2e1083 X0
             have r₂ := b2e21
             grind)
          | (have r₁ := b2e1083 (M.op (σ y) (σ y))
             have r₂ := b2e21
             grind)
          | exact resolve b2e1083 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1083
        have b2e1115 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1109 X0
             have i₂ := b2e37 (σ y)
             grind)
          | exact superpose b2e37 b2e1109
          | (have j0 := b2e1109 X0
             grind)
          | (have r₁ := b2e1109 y
             have r₂ := b2e37 (σ y)
             grind)
          | exact resolve b2e1109 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e1109
        have b2e1118 : ∀ X0 : G, (σ y) = X0 ∨ y ≠ X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1115 X0
             have i₂ := b2e182 X0
             grind)
          | exact superpose b2e182 b2e1115
          | (have j0 := b2e1115 X0
             grind)
          | (have r₁ := b2e1115 (k y (σ y))
             have r₂ := b2e182 y
             grind)
          | exact resolve b2e1115 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182 b2e1115
        have b2e1119 : ∀ X0 : G, y ≠ X0 ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b2e1118 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1118
        have b2e1401 : y = (σ y) := by
          first
          | (have j0 := b2e1119 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1119
        have b2e1402 : False := by grind
        exact b2e1402
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) x (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (σ y)
             have i₂ := b3e27 X0
             grind)
          | exact superpose b3e27 b3e12
          | exact resolve b3e12 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e33 X0 x
             have i₂ := b3e27 x
             grind)
          | exact superpose b3e27 b3e33
          | exact resolve b3e33 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e38 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e27 (σ y)
             grind)
          | exact superpose b3e27 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e27 (σ y)
             grind)
          | exact resolve b3e15 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e39 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e48 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e34 y
             grind)
          | exact superpose b3e34 b3e20
          | exact resolve b3e20 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e39 (σ X0)
             grind)
          | exact superpose b3e39 b3e18
          | exact resolve b3e18 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e16 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X0
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e99 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e106 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e105 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e111 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 ∨ (σ y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e106 X0 X1
             have i₂ := b3e34 X0
             grind)
          | exact superpose b3e34 b3e106
          | (have j0 := b3e106 X0 X1
             grind)
          | exact resolve b3e106 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e207 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e54 X0
             grind)
          | exact superpose b3e54 b3e13
          | exact resolve b3e13 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e208 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e207 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e207
          | exact resolve b3e207 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e207
        have b3e800 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e111 y X0
             have i₂ := b3e208 X0
             grind)
          | exact superpose b3e208 b3e111
          | (have j0 := b3e111 y x
             grind)
          | exact resolve b3e111 b3e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111
        have b3e821 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e800 X0
             grind)
          | (have r₁ := b3e800 (σ y)
             have r₂ := b3e48
             grind)
          | (have r₁ := b3e800 X0
             have r₂ := b3e48
             grind)
          | exact resolve b3e800 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e800
        have b3e829 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ y = (M.op y y) ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e821 X0
             grind)
          | exact superpose b3e821 b3e16
          | (have j0 := b3e16 X0 y
             have j1 := b3e821 y
             grind)
          | (have r₁ := b3e16 (M.op y y) y
             have r₂ := b3e821 (M.op y y)
             grind)
          | exact resolve b3e16 b3e821
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e821
        have b3e843 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e829 X0
             grind)
          | (have r₁ := b3e829 X0
             have r₂ := b3e20
             grind)
          | (have r₁ := b3e829 (M.op y y)
             have r₂ := b3e20
             grind)
          | exact resolve b3e829 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e829
        have b3e845 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e843 X0
             have i₂ := b3e34 y
             grind)
          | exact superpose b3e34 b3e843
          | (have j0 := b3e843 X0
             grind)
          | (have r₁ := b3e843 (σ y)
             have r₂ := b3e34 y
             grind)
          | exact resolve b3e843 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e843
        have b3e846 : ∀ X0 : G, y = X0 ∨ (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e845 X0
             have i₂ := b3e208 X0
             grind)
          | exact superpose b3e208 b3e845
          | (have j0 := b3e845 X0
             grind)
          | (have r₁ := b3e845 (k (σ y) y)
             have r₂ := b3e208 (σ y)
             grind)
          | exact resolve b3e845 b3e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e208 b3e845
        have b3e847 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e846 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e846
        have b3e876 : y = (σ y) := by
          first
          | (have j0 := b3e847 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e847
        have b3e877 : False := by grind
        exact b3e877
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
          have b4e31 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X1 X0 x
               have i₂ := b4e13 X1 x X1
               grind)
            | (have i₁ := b4e31 X0 X1 (M.op X0 X0)
               have i₂ := b4e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b4e13 b4e31
            | exact resolve b4e31 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X2 X1
               have i₂ := b4e33 X1 X0
               grind)
            | (have i₁ := b4e16 X2 X1
               have i₂ := b4e33 X0 X1
               grind)
            | exact superpose b4e33 b4e16
            | (have j0 := b4e16 X2 X1
               grind)
            | (have r₁ := b4e16 X0 (M.op X1 X1)
               have r₂ := b4e33 (M.op X1 X1) X1
               grind)
            | (have r₁ := b4e16 X0 (M.op X0 X0)
               have r₂ := b4e33 X0 (M.op X0 X0)
               grind)
            | exact resolve b4e16 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e61 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e68 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e26
               have i₂ := b4e33 (σ y) X0
               grind)
            | (have i₁ := b4e26
               have i₂ := b4e33 X0 (σ y)
               grind)
            | exact superpose b4e33 b4e26
            | exact resolve b4e26 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e85 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e68 X1
               have i₂ := b4e33 y X0
               grind)
            | (have i₁ := b4e68 X1
               have i₂ := b4e33 X0 y
               grind)
            | exact superpose b4e33 b4e68
            | exact resolve b4e68 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e89 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 (M.op X0 X2)
               have i₂ := b4e13 X0 (M.op X0 X2) X2
               grind)
            | exact superpose b4e13 b4e17
            | (have j0 := b4e17 X2 (M.op X0 X1)
               grind)
            | exact resolve b4e17 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e109 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e89 X0 X1 X2
               grind)
            | (have r₁ := b4e89 X0 X2 X1
               have r₂ := b4e13 X0 X1 X2
               grind)
            | exact resolve b4e89 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e137 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e143 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e137 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e144 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e143
          have b4e191 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (σ (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e85 X1 X3
               have i₂ := b4e13 X1 X0 X2
               grind)
            | exact superpose b4e13 b4e85
            | exact resolve b4e85 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e476 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e54 X0 (M.op X1 X1) X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e516 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e61 X0 (M.op X1 X1)
               have i₂ := b4e476 (τ X0) X1
               grind)
            | exact superpose b4e476 b4e61
            | exact resolve b4e61 b4e476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e517 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e516 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e516
            | exact resolve b4e516 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e516
          have b4e750 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e109 X0 X1 X2
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e109 X0 X1 X2
               grind)
            | exact superpose b4e109 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e109 X0 X1 X2
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e109 X1 X1 X2
               grind)
            | exact resolve b4e17 b4e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e776 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e61 X2 (M.op X0 X1)
               have i₂ := b4e109 X0 X1 (τ X2)
               grind)
            | exact superpose b4e109 b4e61
            | (have j1 := b4e109 X0 X1 X2
               grind)
            | exact resolve b4e61 b4e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e109
          have b4e780 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e750 X0 X1 X2
               grind)
            | (have r₁ := b4e750 X0 X1 X2
               have r₂ := b4e33 X0 X1
               grind)
            | (have r₁ := b4e750 X1 X0 X2
               have r₂ := b4e33 X0 X1
               grind)
            | exact resolve b4e750 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e750
          have b4e841 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e144 (σ (M.op X1 X1)) X0
               have i₂ := b4e517 X0 X1
               grind)
            | exact superpose b4e517 b4e144
            | (have j0 := b4e144 (σ (M.op X1 X1)) X1
               grind)
            | exact resolve b4e144 b4e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144
          have b4e916 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e841 X0 X1
               grind)
            | (have r₁ := b4e841 (σ (M.op X0 X0)) X0
               have r₂ := b4e85 X0 (σ (M.op X0 X0))
               grind)
            | (have r₁ := b4e841 X0 X0
               have r₂ := b4e85 X0 (σ (M.op X0 X0))
               grind)
            | (have r₁ := b4e841 (M.op X1 X1) X0
               have r₂ := b4e85 X0 X1
               grind)
            | exact resolve b4e841 b4e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e841
          have b4e7579 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (k X3 (σ (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e85 X0 X2
               have i₂ := b4e776 X0 X1 X3
               grind)
            | (have i₁ := b4e85 X1 X1
               have i₂ := b4e776 X1 X1 X2
               grind)
            | exact superpose b4e776 b4e85
            | (have j1 := b4e776 X0 X1 X3
               grind)
            | exact resolve b4e85 b4e776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e776
          have b4e10842 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = (k X0 (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e780 X0 (σ (M.op X1 X1)) X2
               have i₂ := b4e916 X0 X1
               grind)
            | exact superpose b4e916 b4e780
            | (have j0 := b4e780 X0 (σ (M.op X1 X1)) X2
               have j1 := b4e916 (σ (M.op X1 X1)) X1
               grind)
            | exact resolve b4e780 b4e916
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e780 b4e916
          have b4e10865 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (σ (M.op X1 X1)) = (k X0 (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e10842 X0 X1 X2
               have j1 := b4e7579 X1 X1 X2 X0
               grind)
            | (have r₁ := b4e10842 X0 X1 X2
               have r₂ := b4e7579 X1 X1 (σ (M.op X1 X1)) x
               grind)
            | (have r₁ := b4e10842 (M.op X2 X2) X1 X2
               have r₂ := b4e7579 X1 X1 X2 x
               grind)
            | exact resolve b4e10842 b4e7579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7579 b4e10842
          have b4e10887 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = X0 ∨ (k X2 X0) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e10865 X0 X1 X2
               have i₂ := b4e517 X0 X1
               grind)
            | exact superpose b4e517 b4e10865
            | (have j0 := b4e10865 X0 X1 X2
               grind)
            | exact resolve b4e10865 b4e517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e517 b4e10865
          have b4e10888 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = X0 ∨ (k X2 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e10887 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10887
          have b4e11828 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e476 X1 X0
               have i₂ := b4e10888 (M.op X0 X0) X2 X1
               grind)
            | exact superpose b4e10888 b4e476
            | (have j1 := b4e10888 (M.op X0 X0) X2 X2
               grind)
            | exact resolve b4e476 b4e10888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e476 b4e10888
          have b4e11872 : ∀ X0 X1 : G, (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e11828 X0 X1 x
               grind)
            | (have r₁ := b4e11828 X1 (σ (M.op X0 X0)) x
               have r₂ := b4e85 X0 X1
               grind)
            | (have r₁ := b4e11828 X1 X1 X0
               have r₂ := b4e85 X0 X1
               grind)
            | exact resolve b4e11828 b4e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85 b4e11828
          have b4e12954 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e191 x x x X0
               have i₂ := b4e11872 X1 (σ (M.op x (M.op x x)))
               grind)
            | exact superpose b4e11872 b4e191
            | (have r₁ := b4e191 X0 X1 x X0
               have r₂ := b4e11872 X0 (σ (M.op X0 (M.op X1 x)))
               grind)
            | exact resolve b4e191 b4e11872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191 b4e11872
          have b4e13090 : False := by grind
          exact b4e13090
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X1 X0 x
               have i₂ := b5e13 X1 x X1
               grind)
            | (have i₁ := b5e30 X0 X1 (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b5e13 b5e30
            | exact resolve b5e30 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e50 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e32 (σ y) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e32 X0 (σ y)
               grind)
            | exact superpose b5e32 b5e23
            | exact resolve b5e23 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e64 : ∀ X0 X1 X2 : G, (σ y) ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e50 X1
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e50
            | exact resolve b5e50 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e88 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e97 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e88
          have b5e103 : y = (k x y) := by
            first
            | (have r₁ := b5e97
               have r₂ := b5e21
               grind)
            | exact resolve b5e97 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b5e2614 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e115 x y
               grind)
            | exact superpose b5e115 b5e24
            | (have j1 := b5e115 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e115 x y
               grind)
            | exact resolve b5e24 b5e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e115
          have b5e2753 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e2614
          have b5e2773 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e2753
               have r₂ := b5e23
               grind)
            | exact resolve b5e2753 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2753
          have b5e2786 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2773
               have i₂ := b5e103
               grind)
            | exact superpose b5e103 b5e2773
            | exact resolve b5e2773 b5e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103 b5e2773
          have b5e2805 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e64 X0 (σ x) (σ y)
               have i₂ := b5e2786
               grind)
            | exact superpose b5e2786 b5e64
            | exact resolve b5e64 b5e2786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e3299 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e2805 (σ x)
               have i₂ := b5e2786
               grind)
            | exact superpose b5e2786 b5e2805
            | (have r₁ := b5e2805 (σ x)
               have r₂ := b5e2786
               grind)
            | exact resolve b5e2805 b5e2786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2786 b5e2805
          have b5e3300 : False := by grind
          exact b5e3300
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (σ y)
             have i₂ := b6e25 X0
             grind)
          | exact superpose b6e25 b6e12
          | exact resolve b6e12 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e30 X0 x
             have i₂ := b6e25 x
             grind)
          | exact superpose b6e25 b6e30
          | exact resolve b6e30 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e35 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e25 (σ y)
             grind)
          | exact superpose b6e25 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e25 (σ y)
             grind)
          | exact resolve b6e15 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e45 : y ≠ (σ y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e31 y
             grind)
          | exact superpose b6e31 b6e20
          | exact resolve b6e20 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e36 (σ X0)
             grind)
          | exact superpose b6e36 b6e18
          | exact resolve b6e18 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e16 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e92 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e99 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e98 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e98
        have b6e104 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 ∨ (σ y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e99 X0 X1
             have i₂ := b6e31 X0
             grind)
          | exact superpose b6e31 b6e99
          | (have j0 := b6e99 X0 X1
             grind)
          | exact resolve b6e99 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e210 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e50 X0
             grind)
          | exact superpose b6e50 b6e13
          | exact resolve b6e13 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e211 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e210 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e210
          | exact resolve b6e210 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e210
        have b6e776 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e104 y X0
             have i₂ := b6e211 X0
             grind)
          | exact superpose b6e211 b6e104
          | (have j0 := b6e104 y x
             grind)
          | exact resolve b6e104 b6e211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e797 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e776 X0
             grind)
          | (have r₁ := b6e776 (σ y)
             have r₂ := b6e45
             grind)
          | (have r₁ := b6e776 X0
             have r₂ := b6e45
             grind)
          | exact resolve b6e776 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e776
        have b6e803 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ y = (M.op y y) ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e16 X0 y
             have i₂ := b6e797 X0
             grind)
          | exact superpose b6e797 b6e16
          | (have j0 := b6e16 X0 y
             have j1 := b6e797 y
             grind)
          | (have r₁ := b6e16 (M.op y y) y
             have r₂ := b6e797 (M.op y y)
             grind)
          | exact resolve b6e16 b6e797
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e797
        have b6e817 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e803 X0
             grind)
          | (have r₁ := b6e803 X0
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e803 (M.op y y)
             have r₂ := b6e20
             grind)
          | exact resolve b6e803 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e803
        have b6e820 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = (k X0 y) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e817 X0
             have i₂ := b6e31 y
             grind)
          | exact superpose b6e31 b6e817
          | (have j0 := b6e817 X0
             grind)
          | (have r₁ := b6e817 (σ y)
             have r₂ := b6e31 y
             grind)
          | exact resolve b6e817 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31 b6e817
        have b6e821 : ∀ X0 : G, y = X0 ∨ (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b6e820 X0
             have i₂ := b6e211 X0
             grind)
          | exact superpose b6e211 b6e820
          | (have j0 := b6e820 X0
             grind)
          | (have r₁ := b6e820 (k (σ y) y)
             have r₂ := b6e211 (σ y)
             grind)
          | exact resolve b6e820 b6e211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e211 b6e820
        have b6e822 : ∀ X0 : G, (σ y) ≠ X0 ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b6e821 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e821
        have b6e895 : y = (σ y) := by
          first
          | (have j0 := b6e822 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e822
        have b6e896 : False := by grind
        exact b6e896
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e29 X1 X0 x
               have i₂ := b7e13 X1 x X1
               grind)
            | (have i₁ := b7e29 X0 X1 (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b7e13 b7e29
            | exact resolve b7e29 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e49 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e31 y X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e31 X0 y
               grind)
            | exact superpose b7e31 b7e21
            | exact resolve b7e21 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e56 : ∀ X0 X1 X2 : G, y ≠ (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e49 X1
               have i₂ := b7e13 X1 X0 X2
               grind)
            | exact superpose b7e13 b7e49
            | exact resolve b7e49 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e88 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ y) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e90 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e88
          have b7e95 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e23
               grind)
            | exact resolve b7e90 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e101 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e95
            | exact resolve b7e95 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e143 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e14
            | exact resolve b7e14 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e144 : y = (k x y) := by
            first
            | (have i₁ := b7e143
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e143
            | exact resolve b7e143 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e157 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e144
               grind)
            | exact superpose b7e144 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e144
          have b7e158 : y = (M.op x y) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b7e157
               have r₂ := b7e22
               grind)
            | exact resolve b7e157 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e157
          have b7e160 : y = (M.op x y) := by
            first
            | (have r₁ := b7e158
               have r₂ := b7e21
               grind)
            | exact resolve b7e158 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e158
          have b7e176 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e56 X0 x y
               have i₂ := b7e160
               grind)
            | exact superpose b7e160 b7e56
            | exact resolve b7e56 b7e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e263 : y ≠ y := by
            first
            | (have i₁ := b7e176 x
               have i₂ := b7e160
               grind)
            | exact superpose b7e160 b7e176
            | (have r₁ := b7e176 x
               have r₂ := b7e160
               grind)
            | exact resolve b7e176 b7e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e160 b7e176
          have b7e264 : False := by grind
          exact b7e264
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e107 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b8e2307 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e107 x y
               grind)
            | exact superpose b8e107 b8e24
            | (have j1 := b8e107 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e107 x y
               grind)
            | exact resolve b8e24 b8e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e2440 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b8e2307
          have b8e2460 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e2440
               have r₂ := b8e23
               grind)
            | exact resolve b8e2440 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2440
          have b8e2478 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2460
               grind)
            | exact superpose b8e2460 b8e20
            | exact resolve b8e20 b8e2460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2460
          have b8e2725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e2478
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2478
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e2478 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2478
          have b8e2726 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b8e2725
          have b8e2730 : y = (M.op y y) := by
            first
            | (have r₁ := b8e2726
               have r₂ := b8e22
               grind)
            | exact resolve b8e2726 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2726
          have b8e2734 : False := by grind
          exact b8e2734

/-- `Equation318`: `x ◇ x = y ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation318 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law318 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law318.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : (M.op x y) = (k x y) := by grind
      have b0e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e46 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e38
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e46
        | exact resolve b0e46 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e46
      have b0e49 : False := by grind
      exact b0e49
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) x (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e28 (σ y)
             grind)
          | exact superpose b1e28 b1e21
          | exact resolve b1e21 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b1e48 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e45
          | exact resolve b1e45 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e51 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e28 (σ y)
             grind)
          | exact superpose b1e28 b1e48
          | exact resolve b1e48 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e48
        have b1e148 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e51
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e51 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e152 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e148
        have b1e156 : (σ x) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e152
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e152
          | exact resolve b1e152 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e152
        have b1e157 : y = (M.op y y) := by
          first
          | (have r₁ := b1e156
             have r₂ := b1e37
             grind)
          | exact resolve b1e156 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e156
        have b1e254 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e157
             grind)
          | exact superpose b1e157 b1e20
          | exact resolve b1e20 b1e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e157
        have b1e383 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e254
             grind)
          | exact superpose b1e254 b1e37
          | exact resolve b1e37 b1e254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e254
        have b1e390 : False := by grind
        exact b1e390
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e35 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e38 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          grind
        have b2e41 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e38 X0 X1
             have i₂ := b2e12 X0 (M.op X0 X0) X1
             grind)
          | (have i₁ := b2e38 X0 X0
             have i₂ := b2e12 (M.op X0 X0) X1 x
             grind)
          | exact superpose b2e12 b2e38
          | exact resolve b2e38 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e79 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ x) (σ x)) x
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e35 X1 X0
             grind)
          | exact superpose b2e35 b2e13
          | exact resolve b2e13 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e316 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          grind
        clear b2e41
        have b2e335 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e316 X0 x
             have i₂ := b2e12 X0 x X0
             grind)
          | (have i₁ := b2e316 X0 (M.op X0 X0)
             have i₂ := b2e12 (M.op X0 X0) x x
             grind)
          | exact superpose b2e12 b2e316
          | (have j0 := b2e316 X0 x
             grind)
          | exact resolve b2e316 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e316
        have b2e336 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e335 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e335
        have b2e376 : y = (k y x) := by
          first
          | (have i₁ := b2e336 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e336
          | exact resolve b2e336 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e380 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e336 X2
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e336
          | exact resolve b2e336 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e336
        have b2e521 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e111 X0 (M.op X1 (M.op X2 (σ X0)))
             have i₂ := b2e380 X1 X2 (σ X0)
             grind)
          | exact superpose b2e380 b2e111
          | exact resolve b2e111 b2e380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e111 b2e380
        have b2e524 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e521 X0 X1 X2
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e521
          | exact resolve b2e521 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e521
        have b2e1787 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b2e79 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e1788 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e1787
             have r₂ := b2e21
             grind)
          | exact resolve b2e1787 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1787
        have b2e1789 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e1788
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e1788
          | exact resolve b2e1788 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1788
        have b2e1790 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1789
             have i₂ := b2e376
             grind)
          | exact superpose b2e376 b2e1789
          | exact resolve b2e1789 b2e376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e376 b2e1789
        have b2e1792 : ∀ X0 : G, y = (k y (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e524 y X0 (σ x)
             have i₂ := b2e1790
             grind)
          | exact superpose b2e1790 b2e524
          | exact resolve b2e524 b2e1790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e524
        have b2e2231 : y = (k y (τ (σ y))) := by
          first
          | (have i₁ := b2e1792 (σ x)
             have i₂ := b2e1790
             grind)
          | exact superpose b2e1790 b2e1792
          | exact resolve b2e1792 b2e1790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1792
        have b2e2243 : y = (k y y) := by
          first
          | (have i₁ := b2e2231
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e2231
          | exact resolve b2e2231 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2231
        have b2e2261 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e81 y y
             have i₂ := b2e2243
             grind)
          | exact superpose b2e2243 b2e81
          | (have j0 := b2e81 y y
             grind)
          | exact resolve b2e81 b2e2243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81 b2e2243
        have b2e2264 : y = (M.op y y) := by grind
        clear b2e2261
        have b2e2281 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e2264
             grind)
          | exact superpose b2e2264 b2e20
          | exact resolve b2e20 b2e2264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2264
        have b2e2757 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2281
             grind)
          | exact superpose b2e2281 b2e22
          | exact resolve b2e22 b2e2281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2768 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1790
             have i₂ := b2e2281
             grind)
          | exact superpose b2e2281 b2e1790
          | exact resolve b2e1790 b2e2281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1790 b2e2281
        have b2e2774 : False := by grind
        exact b2e2774
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 x x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) x (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e27 y
             grind)
          | exact superpose b3e27 b3e20
          | exact resolve b3e20 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        have b3e47 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e50 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e28 (σ x)
             grind)
          | exact superpose b3e28 b3e47
          | exact resolve b3e47 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e47
        have b3e127 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e13
          | exact resolve b3e13 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e129 : x = (k x x) := by
          first
          | (have i₁ := b3e127
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e127
          | exact resolve b3e127 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127
        have b3e146 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e129
             grind)
          | exact superpose b3e129 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129
        have b3e147 : x = (M.op x x) := by grind
        clear b3e146
        have b3e149 : x = y := by
          first
          | (have i₁ := b3e147
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e147
          | exact resolve b3e147 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e147
        have b3e151 : False := by grind
        exact b3e151
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, y = (M.op X0 y) := by
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
          have b4e30 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) x (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e118 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e30 (σ x)
               grind)
            | exact superpose b4e30 b4e20
            | exact resolve b4e20 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e119 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e118
               have i₂ := b4e29 x
               grind)
            | exact superpose b4e29 b4e118
            | exact resolve b4e118 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e118
          have b4e120 : False := by grind
          exact b4e120
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e37 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e29 y
               grind)
            | exact superpose b5e29 b5e21
            | exact resolve b5e21 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e41 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            grind
          have b5e44 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1
               have i₂ := b5e13 X0 (M.op X0 X0) X1
               grind)
            | (have i₁ := b5e41 X0 X0
               have i₂ := b5e13 (M.op X0 X0) X1 x
               grind)
            | exact superpose b5e13 b5e41
            | exact resolve b5e41 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e45 : x = (M.op y y) ∨ x = (k x y) := by grind
          have b5e60 : x = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e81 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ y) (σ x)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e114 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e35 X1 X0
               grind)
            | exact superpose b5e35 b5e14
            | exact resolve b5e14 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e319 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            grind
          clear b5e44
          have b5e338 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e319 X0 x
               have i₂ := b5e13 X0 x X0
               grind)
            | (have i₁ := b5e319 X0 (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) x x
               grind)
            | exact superpose b5e13 b5e319
            | (have j0 := b5e319 X0 x
               grind)
            | exact resolve b5e319 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e319
          have b5e339 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e338 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e338
          have b5e383 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e339 X2
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e339
            | exact resolve b5e339 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e339
          have b5e485 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e114 X0 (M.op X1 (M.op X2 (σ X0)))
               have i₂ := b5e383 X1 X2 (σ X0)
               grind)
            | exact superpose b5e383 b5e114
            | exact resolve b5e114 b5e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e114 b5e383
          have b5e488 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e485 X0 X1 X2
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e485
            | exact resolve b5e485 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e485
          have b5e2201 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e81 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e2202 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e2201
               have r₂ := b5e24
               grind)
            | exact resolve b5e2201 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2201
          have b5e2203 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2202
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2202
            | exact resolve b5e2202 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2202
          have b5e2204 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e2203
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e2203
            | exact resolve b5e2203 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e2203
          have b5e2205 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b5e488 x X0 (σ y)
               have i₂ := b5e2204
               grind)
            | exact superpose b5e2204 b5e488
            | exact resolve b5e488 b5e2204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e488
          have b5e2241 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b5e2205 (σ y)
               have i₂ := b5e2204
               grind)
            | exact superpose b5e2204 b5e2205
            | exact resolve b5e2205 b5e2204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2204 b5e2205
          have b5e2253 : x = (k x x) := by
            first
            | (have i₁ := b5e2241
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e2241
            | exact resolve b5e2241 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2241
          have b5e2467 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e84 x x
               have i₂ := b5e2253
               grind)
            | exact superpose b5e2253 b5e84
            | (have j0 := b5e84 x x
               grind)
            | exact resolve b5e84 b5e2253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e2253
          have b5e2470 : x = (M.op x x) := by grind
          clear b5e2467
          have b5e2746 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e2470
               grind)
            | exact superpose b5e2470 b5e22
            | exact resolve b5e22 b5e2470
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2470
          have b5e2785 : False := by grind
          exact b5e2785
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e38 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          grind
        have b6e39 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        have b6e40 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e41 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e38 X0 X1
             have i₂ := b6e12 X0 (M.op X0 X0) X1
             grind)
          | (have i₁ := b6e38 X0 X0
             have i₂ := b6e12 (M.op X0 X0) X1 x
             grind)
          | exact superpose b6e12 b6e38
          | exact resolve b6e38 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b6e43 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e27 (σ x)
             grind)
          | exact superpose b6e27 b6e40
          | exact resolve b6e40 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e40
        have b6e46 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e13
          | exact resolve b6e13 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e47 : x = (k x x) := by
          first
          | (have i₁ := b6e46
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e46
          | exact resolve b6e46 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e100 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e101 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e47
             have i₂ := b6e17 x x
             grind)
          | exact superpose b6e17 b6e47
          | (have j1 := b6e17 x x
             grind)
          | exact resolve b6e47 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e104 : x = (M.op x x) := by grind
        clear b6e101
        have b6e115 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e12 x x x
             have i₂ := b6e104
             grind)
          | exact superpose b6e104 b6e12
          | exact resolve b6e12 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e138 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e19
          | exact resolve b6e19 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e141 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e138
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e138
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e138 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138
        have b6e142 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e141
             have r₂ := b6e20
             grind)
          | exact resolve b6e141 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e143 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have r₁ := b6e142
             have r₂ := b6e21
             grind)
          | exact resolve b6e142 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142
        have b6e144 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e143
             have i₂ := b6e115 y
             grind)
          | exact superpose b6e115 b6e143
          | exact resolve b6e143 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e143
        have b6e380 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X0))) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          grind
        have b6e410 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e380 X0 x
             have i₂ := b6e12 X0 x X0
             grind)
          | (have i₁ := b6e380 X0 (M.op X0 X0)
             have i₂ := b6e12 (M.op X0 X0) x x
             grind)
          | exact superpose b6e12 b6e380
          | (have j0 := b6e380 X0 x
             grind)
          | exact resolve b6e380 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e380
        have b6e411 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e410 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e410
        have b6e435 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e411 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e411
          | exact resolve b6e411 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e411
        have b6e439 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e435
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e435
          | exact resolve b6e435 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e435
        have b6e484 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e439
             grind)
          | exact superpose b6e439 b6e13
          | exact resolve b6e13 b6e439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e439
        have b6e485 : y = (k y x) := by
          first
          | (have i₁ := b6e484
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e484
          | exact resolve b6e484 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e484
        have b6e498 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e485
             grind)
          | exact superpose b6e485 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e485
        have b6e499 : y = (M.op x y) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e498
             have r₂ := b6e21
             grind)
          | exact resolve b6e498 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e498
        have b6e501 : y = (M.op x y) := by
          first
          | (have r₁ := b6e499
             have r₂ := b6e20
             grind)
          | exact resolve b6e499 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e499
        have b6e580 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e144
             have i₂ := b6e501
             grind)
          | exact superpose b6e501 b6e144
          | exact resolve b6e144 b6e501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e581 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 x
             have i₂ := b6e501
             grind)
          | exact superpose b6e501 b6e12
          | exact resolve b6e12 b6e501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e768 : y = (M.op y y) := by
          first
          | (have i₁ := b6e501
             have i₂ := b6e581 x
             grind)
          | exact superpose b6e581 b6e501
          | exact resolve b6e501 b6e581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e501 b6e581
        have b6e1095 : y = (k y y) := by
          first
          | (have i₁ := b6e41 y y
             have i₂ := b6e768
             grind)
          | exact superpose b6e768 b6e41
          | exact resolve b6e41 b6e768
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e768
        have b6e3812 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e100 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e100
          | exact resolve b6e100 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100
        have b6e4139 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e3812
        have b6e4220 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b6e4139
             have r₂ := b6e580
             grind)
          | exact resolve b6e4139 b6e580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4139
        have b6e4272 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4220
             have i₂ := b6e1095
             grind)
          | exact superpose b6e1095 b6e4220
          | exact resolve b6e4220 b6e1095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1095 b6e4220
        have b6e4298 : False := by grind
        exact b6e4298
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 X0)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) x (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e29 (σ x)
               grind)
            | exact superpose b7e29 b7e20
            | exact resolve b7e20 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
          have b7e44 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e29 (σ y)
               grind)
            | exact superpose b7e29 b7e44
            | exact resolve b7e44 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e44
          have b7e141 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e143 : y = (k y y) := by
            first
            | (have i₁ := b7e141
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e141
            | exact resolve b7e141 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e149 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e143
               grind)
            | exact superpose b7e143 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e150 : y = (M.op y y) := by grind
          clear b7e149
          have b7e232 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e13 y x y
               have i₂ := b7e150
               grind)
            | exact superpose b7e150 b7e13
            | exact resolve b7e13 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e401 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e232 x
               grind)
            | exact superpose b7e232 b7e39
            | exact resolve b7e39 b7e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e232
          have b7e403 : False := by grind
          exact b7e403
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e83 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ x)
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
          have b8e2364 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e83 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e2365 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e2364
               have r₂ := b8e23
               grind)
            | exact resolve b8e2364 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2364
          have b8e2366 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e2365
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e2365
            | exact resolve b8e2365 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2365
          have b8e2367 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2366
               grind)
            | exact superpose b8e2366 b8e20
            | exact resolve b8e20 b8e2366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2366
          have b8e2595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e2367
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e2367
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e2367 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2367
          have b8e2609 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e2595
          have b8e2618 : x = (M.op y y) := by
            first
            | (have r₁ := b8e2609
               have r₂ := b8e22
               grind)
            | exact resolve b8e2609 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2609
          have b8e2622 : False := by grind
          exact b8e2622

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyy_y_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
        have b1e26 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
        have b1e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e29 X0 X1
             grind)
          | exact superpose b1e29 b1e13
          | exact resolve b1e13 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : y ≠ y ∨ (k x y) = (M.op y y) := by
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
        have b1e37 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X0 (M.op X1 X2)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b1e15 X0 (M.op X0 X0)
             have r₂ := b1e12 X0 X0 X0
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (k X0 x) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 x
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e15
          | (have j0 := b1e15 X0 x
             grind)
          | exact resolve b1e15 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (k x y) = (M.op y y) := by grind
        clear b1e35
        have b1e40 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x ≠ (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e38 X0
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e38
          | (have j0 := b1e38 X0
             grind)
          | exact resolve b1e38 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e41 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e37 X0 X1 X2
             have i₂ := b1e12 (M.op X1 X2) X1 X2
             grind)
          | exact superpose b1e12 b1e37
          | (have j0 := b1e37 X0 X1 X2
             grind)
          | (have r₁ := b1e37 X0 X0 (M.op X0 X2)
             have r₂ := b1e12 X0 X0 X2
             grind)
          | (have r₁ := b1e37 (M.op X1 X2) (M.op X1 X2) X1
             have r₂ := b1e12 (M.op X1 X2) X1 X2
             grind)
          | exact resolve b1e37 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e42 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ y = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e40 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e40
          | (have j0 := b1e40 X0
             grind)
          | exact resolve b1e40 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e45 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ x = (M.op X0 y) ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 x
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e16
          | (have j0 := b1e16 X0 y
             grind)
          | exact resolve b1e16 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e47 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e23
             grind)
          | exact resolve b1e46 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e48
          | exact resolve b1e48 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e52 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e13
          | exact resolve b1e13 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e53 : y = (M.op y y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e52
          | exact resolve b1e52 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e29 X0 X1
             have i₂ := b1e17 (τ X0) X1
             grind)
          | exact superpose b1e17 b1e29
          | (have j1 := b1e17 (τ X0) X1
             grind)
          | exact resolve b1e29 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e61 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e15
          | (have r₁ := b1e15 y y
             have r₂ := b1e53
             grind)
          | exact resolve b1e15 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : y = (k y y) := by grind
        clear b1e61
        have b1e69 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e30 X1 X0
             grind)
          | exact superpose b1e30 b1e13
          | exact resolve b1e13 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e78 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ (k (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e41 (σ x) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e41
          | (have j0 := b1e41 (σ x) (σ y) X0
             grind)
          | exact resolve b1e41 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e86 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e41 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e91 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e34 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e34
          | exact resolve b1e34 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e109 : x ≠ y ∨ y = (k x x) := by
          first
          | (have i₁ := b1e42 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e42
          | (have j0 := b1e42 x
             grind)
          | exact resolve b1e42 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e125 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 (σ X0) (σ X1)
             have i₂ := b1e58 X0 X1
             grind)
          | exact superpose b1e58 b1e12
          | (have j1 := b1e58 X0 X1
             grind)
          | exact resolve b1e12 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e127 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e151 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e86 (σ x)
             have i₂ := b1e58 x x
             grind)
          | exact superpose b1e58 b1e86
          | (have j1 := b1e58 X0 X0
             grind)
          | exact resolve b1e86 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e86
        have b1e157 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e151 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e151
        have b1e159 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e157 X0
             have i₂ := b1e18 X0 (k X0 X0)
             grind)
          | exact superpose b1e18 b1e157
          | (have j0 := b1e157 X0
             grind)
          | exact resolve b1e157 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e157
        have b1e234 : y ≠ y ∨ x = y ∨ x = (k y x) := by
          first
          | (have i₁ := b1e45 y
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e45
          | (have j0 := b1e45 y
             grind)
          | (have r₁ := b1e45 y
             have r₂ := b1e53
             grind)
          | exact resolve b1e45 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e235 : x = (k y x) ∨ x = y := by grind
        clear b1e234
        have b1e521 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e59 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e59
          | exact resolve b1e59 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e529 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (τ X0) y) ∨ x = (M.op (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e59 X0 x
             have i₂ := b1e26 (τ X0)
             grind)
          | exact superpose b1e26 b1e59
          | (have j0 := b1e59 X0 y
             grind)
          | exact resolve b1e59 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e521 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e521
          | (have j0 := b1e521 X0 X1
             grind)
          | exact resolve b1e521 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e521
        have b1e683 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e127 y x
             have i₂ := b1e235
             grind)
          | exact superpose b1e235 b1e127
          | (have j0 := b1e127 y x
             grind)
          | exact resolve b1e127 b1e235
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127
        have b1e686 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
        clear b1e683
        have b1e1187 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 X1))) = (k (σ X2) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e18 X2 (k X0 X1)
             have i₂ := b1e556 X0 X1
             grind)
          | exact superpose b1e556 b1e18
          | (have j1 := b1e556 X0 X1
             grind)
          | exact resolve b1e18 b1e556
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1221 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 X1))) = (σ (k X2 (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1187 X0 X1 X2
             have i₂ := b1e18 X2 (M.op X0 X1)
             grind)
          | exact superpose b1e18 b1e1187
          | (have j0 := b1e1187 X0 X1 X2
             grind)
          | exact resolve b1e1187 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1187
        have b1e1527 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e78 (σ x)
             have i₂ := b1e686
             grind)
          | exact superpose b1e686 b1e78
          | (have r₁ := b1e78 (σ x)
             have r₂ := b1e686
             grind)
          | exact resolve b1e78 b1e686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78 b1e686
        have b1e1539 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
        clear b1e1527
        have b1e1543 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1539
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e1539
          | exact resolve b1e1539 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1539
        have b1e1545 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e1543
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1543
          | exact resolve b1e1543 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1543
        have b1e1638 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e1545
             grind)
          | exact superpose b1e1545 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e1545
             grind)
          | exact resolve b1e16 b1e1545
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1545
        have b1e1647 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by grind
        clear b1e1638
        have b1e1649 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have r₁ := b1e1647
             have r₂ := b1e23
             grind)
          | exact resolve b1e1647 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1647
        have b1e1653 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b1e1649
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e1649
          | exact resolve b1e1649 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1649
        have b1e1812 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b1e556 x x
             have i₂ := b1e1653
             grind)
          | exact superpose b1e1653 b1e556
          | (have j0 := b1e556 x x
             grind)
          | exact resolve b1e556 b1e1653
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e556 b1e1653
        have b1e1837 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by grind
        clear b1e1812
        have b1e1866 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b1e1837
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e1837
          | exact resolve b1e1837 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1837
        have b1e1869 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b1e1866
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1866
          | exact resolve b1e1866 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1866
        have b1e1872 : x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have r₁ := b1e1869
             have r₂ := b1e23
             grind)
          | exact resolve b1e1869 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1869
        have b1e1875 : x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b1e1872
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e1872
          | exact resolve b1e1872 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1872
        have b1e1878 : x = y ∨ (σ x) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b1e1875
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1875
          | exact resolve b1e1875 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1875
        have b1e1879 : (σ x) = (σ (k y x)) ∨ x = y := by grind
        clear b1e1878
        have b1e2045 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k y x) X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e18 (k y x) X0
             have i₂ := b1e1879
             grind)
          | exact superpose b1e1879 b1e18
          | exact resolve b1e18 b1e1879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2058 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (k y x) (τ X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e69 (k y x) X0
             have i₂ := b1e1879
             grind)
          | exact superpose b1e1879 b1e69
          | exact resolve b1e69 b1e1879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1879
        have b1e2075 : ∀ X0 : G, (k x (τ X0)) = (k (k y x) (τ X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e2058 X0
             have i₂ := b1e69 x X0
             grind)
          | exact superpose b1e69 b1e2058
          | exact resolve b1e2058 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69 b1e2058
        have b1e2086 : ∀ X0 : G, (σ (k x X0)) = (σ (k (k y x) X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e2045 X0
             have i₂ := b1e18 x X0
             grind)
          | exact superpose b1e18 b1e2045
          | exact resolve b1e2045 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2045
        have b1e2253 : ∀ X0 : G, (k x X0) = (k (k y x) X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e2075 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2075
          | exact resolve b1e2075 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2075
        have b1e3415 : ∀ X0 X1 : G, (k (τ X1) (k (k y x) X0)) = (τ (k X1 (σ (k x X0)))) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e34 X1 (k (k y x) X0)
             have i₂ := b1e2086 X0
             grind)
          | exact superpose b1e2086 b1e34
          | exact resolve b1e34 b1e2086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2086
        have b1e3445 : ∀ X0 X1 : G, (k (τ X1) (k (k y x) X0)) = (k (τ X1) (k x X0)) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e3415 X0 X1
             have i₂ := b1e34 X1 (k x X0)
             grind)
          | exact superpose b1e34 b1e3415
          | exact resolve b1e3415 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e3415
        have b1e5393 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (σ (k (τ X0) (τ (k X0 X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e159 (τ X0)
             have i₂ := b1e91 X0 X0
             grind)
          | exact superpose b1e91 b1e159
          | (have j0 := b1e159 (τ X0)
             grind)
          | exact resolve b1e159 b1e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91 b1e159
        have b1e5496 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (k (σ (τ X0)) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e5393 X0
             have i₂ := b1e30 (k X0 X0) (τ X0)
             grind)
          | exact superpose b1e30 b1e5393
          | (have j0 := b1e5393 X0
             grind)
          | exact resolve b1e5393 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e5393
        have b1e5528 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (σ (τ (k X0 X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e5496 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e5496
          | (have j0 := b1e5496 X0
             grind)
          | exact resolve b1e5496 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5496
        have b1e5552 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e5528 X0
             have i₂ := b1e14 (k X0 X0)
             grind)
          | exact superpose b1e14 b1e5528
          | (have j0 := b1e5528 X0
             grind)
          | exact resolve b1e5528 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5528
        have b1e5578 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e5552 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e5552
          | (have j0 := b1e5552 X0
             grind)
          | exact resolve b1e5552 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5552
        have b1e6708 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 y)) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e529 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e529
          | exact resolve b1e529 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e529
        have b1e6767 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 y)) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e6708 X0
             have i₂ := b1e18 X0 x
             grind)
          | exact superpose b1e18 b1e6708
          | (have j0 := b1e6708 X0
             grind)
          | exact resolve b1e6708 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6708
        have b1e15662 : ∀ X0 X1 : G, (k X0 (k (k y x) X1)) = (k X0 (k x X1)) ∨ x = y := by
          intro X0 X1
          first
          | (have i₁ := b1e3445 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e3445
          | exact resolve b1e3445 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3445
        have b1e16182 : ∀ X0 : G, (k (k y x) (k x X0)) = (k x (k (k y x) X0)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e2253 (k (k y x) X0)
             have i₂ := b1e15662 (k y x) X0
             grind)
          | exact superpose b1e15662 b1e2253
          | exact resolve b1e2253 b1e15662
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2253 b1e15662
        have b1e16214 : ∀ X0 : G, (k (k y x) (k x X0)) = (k x (k (k y x) X0)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e16182 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16182
        have b1e61277 : ∀ X0 : G, (k X0 x) = (τ (σ (M.op X0 y))) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e13 (k X0 x)
             have i₂ := b1e6767 X0
             grind)
          | exact superpose b1e6767 b1e13
          | (have j1 := b1e6767 X0
             grind)
          | exact resolve b1e13 b1e6767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6767
        have b1e61418 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e61277 X0
             have i₂ := b1e13 (M.op X0 y)
             grind)
          | exact superpose b1e13 b1e61277
          | (have j0 := b1e61277 X0
             grind)
          | exact resolve b1e61277 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61277
        have b1e62164 : (k x (k (k y x) x)) = (k (k y x) (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e16214 x
             have i₂ := b1e61418 x
             grind)
          | exact superpose b1e61418 b1e16214
          | (have j1 := b1e61418 x
             grind)
          | exact resolve b1e16214 b1e61418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16214 b1e61418
        have b1e62290 : (k x (k (k y x) x)) = (k (k y x) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
        clear b1e62164
        have b1e62296 : (k x (k (k y x) x)) = (k (k y x) y) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b1e62290
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e62290
          | exact resolve b1e62290 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62290
        have b1e62305 : x = y ∨ (k x (k (k y x) x)) = (k (k y x) y) ∨ x = y := by
          first
          | (have i₁ := b1e62296
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e62296
          | exact resolve b1e62296 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62296
        have b1e62306 : (k x (k (k y x) x)) = (k (k y x) y) ∨ x = y := by grind
        clear b1e62305
        have b1e62851 : (k x y) = (k x (k x x)) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b1e62306
             have i₂ := b1e235
             grind)
          | exact superpose b1e235 b1e62306
          | exact resolve b1e62306 b1e235
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e235 b1e62306
        have b1e62898 : (k x y) = (k x (k x x)) ∨ x = y := by grind
        clear b1e62851
        have b1e62902 : (M.op y y) = (k x (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e62898
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e62898
          | exact resolve b1e62898 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e62898
        have b1e62905 : y = (k x (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e62902
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e62902
          | exact resolve b1e62902 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62902
        have b1e63446 : y = (M.op (k x x) x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e5578 x
             have i₂ := b1e62905
             grind)
          | exact superpose b1e62905 b1e5578
          | (have j0 := b1e5578 x
             grind)
          | exact resolve b1e5578 b1e62905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5578 b1e62905
        have b1e63475 : y = (M.op (k x x) y) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e63446
             have i₂ := b1e26 (k x x)
             grind)
          | exact superpose b1e26 b1e63446
          | exact resolve b1e63446 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63446
        have b1e63479 : x = (M.op x y) ∨ y = (M.op (k x x) y) ∨ x = y := by
          first
          | (have i₁ := b1e63475
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e63475
          | exact resolve b1e63475 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63475
        have b1e63482 : x = y ∨ y = (M.op (k x x) y) ∨ x = y := by
          first
          | (have i₁ := b1e63479
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e63479
          | exact resolve b1e63479 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63479
        have b1e63483 : y = (M.op (k x x) y) ∨ x = y := by grind
        clear b1e63482
        have b1e64017 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (k x x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (k x x) y
             have i₂ := b1e63483
             grind)
          | exact superpose b1e63483 b1e12
          | exact resolve b1e12 b1e63483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64020 : ∀ X0 : G, y ≠ (M.op X0 (k x x)) ∨ (k X0 y) = (M.op y (k x x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e41 X0 (k x x) y
             have i₂ := b1e63483
             grind)
          | exact superpose b1e63483 b1e41
          | exact resolve b1e41 b1e63483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e63483
        have b1e118089 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k X0 y) = (M.op y (k x x)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b1e64020 X0
             have i₂ := b1e64017 X0
             grind)
          | exact superpose b1e64017 b1e64020
          | (have j0 := b1e64020 X0
             grind)
          | exact resolve b1e64020 b1e64017
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64017 b1e64020
        have b1e118093 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k X0 y) = (M.op y (k x x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b1e118089 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118089
        have b1e118106 : y ≠ y ∨ (k y y) = (M.op y (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e118093 y
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e118093
          | (have j0 := b1e118093 y
             grind)
          | (have r₁ := b1e118093 y
             have r₂ := b1e53
             grind)
          | exact resolve b1e118093 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e118093
        have b1e118107 : (k y y) = (M.op y (k x x)) ∨ x = y := by grind
        clear b1e118106
        have b1e118116 : y = (M.op y (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e118107
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e118107
          | exact resolve b1e118107 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118107
        have b1e118137 : y ≠ y ∨ y = (k x x) ∨ (k x x) = (k y (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e16 y (k x x)
             have i₂ := b1e118116
             grind)
          | exact superpose b1e118116 b1e16
          | (have j0 := b1e16 y (k x x)
             grind)
          | (have r₁ := b1e16 y (k x x)
             have r₂ := b1e118116
             grind)
          | exact resolve b1e16 b1e118116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118116
        have b1e118153 : y = (k x x) ∨ (k x x) = (k y (k x x)) ∨ x = y := by grind
        clear b1e118137
        have b1e118164 : (k x x) = (k y (k x x)) ∨ y = (k x x) := by
          first
          | (have r₁ := b1e118153
             have r₂ := b1e109
             grind)
          | exact resolve b1e118153 b1e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109 b1e118153
        have b1e118332 : (σ (k x x)) = (σ (k y (M.op x x))) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e1221 x x y
             have i₂ := b1e118164
             grind)
          | exact superpose b1e118164 b1e1221
          | (have j0 := b1e1221 x x x
             grind)
          | exact resolve b1e1221 b1e118164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1221 b1e118164
        have b1e118336 : (σ (k x x)) = (σ (k y (M.op x x))) ∨ x = (M.op x x) ∨ y = (k x x) := by grind
        clear b1e118332
        have b1e118339 : (σ (k x x)) = (σ (k y (M.op x y))) ∨ x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e118336
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e118336
          | exact resolve b1e118336 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118336
        have b1e118340 : (σ (k y y)) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e118339
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e118339
          | exact resolve b1e118339 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118339
        have b1e118341 : (σ y) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e118340
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e118340
          | exact resolve b1e118340 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e118340
        have b1e118342 : x = (M.op x y) ∨ (σ y) = (σ (k x x)) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e118341
             have i₂ := b1e26 x
             grind)
          | exact superpose b1e26 b1e118341
          | exact resolve b1e118341 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e118341
        have b1e118343 : (σ y) = (σ (k x x)) ∨ y = (k x x) := by
          first
          | (have j1 := b1e42 x
             grind)
          | (have r₁ := b1e118342
             have r₂ := b1e42 x
             grind)
          | exact resolve b1e118342 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e118342
        have b1e118365 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e118343
             grind)
          | exact superpose b1e118343 b1e13
          | exact resolve b1e13 b1e118343
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118343
        have b1e118427 : y = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e118365
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e118365
          | exact resolve b1e118365 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118365
        have b1e118428 : y = (k x x) := by grind
        clear b1e118427
        have b1e118635 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e125 x x X0
             have i₂ := b1e118428
             grind)
          | exact superpose b1e118428 b1e125
          | (have j0 := b1e125 x x x
             grind)
          | exact resolve b1e125 b1e118428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125
        have b1e118692 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have j0 := b1e118635 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118635
        have b1e122788 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e118692
        have b1e122790 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b1e122788
             have r₂ := b1e22
             grind)
          | exact resolve b1e122788 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122788
        have b1e122829 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e122790
             grind)
          | exact superpose b1e122790 b1e15
          | (have r₁ := b1e15 (σ x) (σ x)
             have r₂ := b1e122790
             grind)
          | exact resolve b1e15 b1e122790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122790
        have b1e122846 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b1e122829
        have b1e122849 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e122846
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e122846
          | exact resolve b1e122846 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122846
        have b1e122856 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e122849
             have i₂ := b1e118428
             grind)
          | exact superpose b1e118428 b1e122849
          | exact resolve b1e122849 b1e118428
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e118428 b1e122849
        have b1e122863 : False := by grind
        exact b1e122863
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
        have b2e24 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
        have b2e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e30 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e18 X2 (k (τ X0) X1)
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e18
          | exact resolve b2e18 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : y ≠ y ∨ (k x y) = (M.op y y) := by
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
        have b2e34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e12 X0 X0 X0
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : (k x y) = (M.op y y) := by grind
        clear b2e33
        have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e34 X0 X1 X2
             have i₂ := b2e12 (M.op X1 X2) X1 X2
             grind)
          | exact superpose b2e12 b2e34
          | (have j0 := b2e34 X0 X1 X2
             grind)
          | (have r₁ := b2e34 X0 X0 (M.op X0 X2)
             have r₂ := b2e12 X0 X0 X2
             grind)
          | (have r₁ := b2e34 (M.op X1 X2) (M.op X1 X2) X1
             have r₂ := b2e12 (M.op X1 X2) X1 X2
             grind)
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e45 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e18 X2 (k X0 (τ X1))
             have i₂ := b2e28 X1 X0
             grind)
          | exact superpose b2e28 b2e18
          | exact resolve b2e18 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e28 X1 X0
             grind)
          | exact superpose b2e28 b2e13
          | exact resolve b2e13 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e54 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e27 X0 X1
             have i₂ := b2e17 (τ X0) X1
             grind)
          | exact superpose b2e17 b2e27
          | (have j1 := b2e17 (τ X0) X1
             grind)
          | exact resolve b2e27 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e60 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 X1
             have i₂ := b2e17 X0 (σ X1)
             grind)
          | exact superpose b2e17 b2e32
          | (have j1 := b2e17 X0 (σ X1)
             grind)
          | exact resolve b2e32 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e71 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e38 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e93 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (σ X0) (σ X1)
             have i₂ := b2e53 X0 X1
             grind)
          | exact superpose b2e53 b2e12
          | (have j1 := b2e53 X0 X1
             grind)
          | exact resolve b2e12 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e95 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e115 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e71 (σ x)
             have i₂ := b2e53 x x
             grind)
          | exact superpose b2e53 b2e71
          | (have j1 := b2e53 X0 X0
             grind)
          | exact resolve b2e71 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e120 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e115 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115
        have b2e121 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e120 X0
             have i₂ := b2e18 X0 (k X0 X0)
             grind)
          | exact superpose b2e18 b2e120
          | (have j0 := b2e120 X0
             grind)
          | exact resolve b2e120 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120
        have b2e143 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e30 X0 X1 X2
             have i₂ := b2e17 X0 (σ X1)
             grind)
          | exact superpose b2e17 b2e30
          | (have j1 := b2e17 X0 (σ X1)
             grind)
          | exact resolve b2e30 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e181 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e45 X0 X1 X2
             have i₂ := b2e17 (σ X0) X1
             grind)
          | exact superpose b2e17 b2e45
          | (have j1 := b2e17 (σ X0) X1
             grind)
          | exact resolve b2e45 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e440 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op X1 X2))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X2) = (M.op (τ X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e54 X0 (M.op X1 X2)
             have i₂ := b2e12 (τ X0) X1 X2
             grind)
          | exact superpose b2e12 b2e54
          | (have j0 := b2e54 X0 X1
             grind)
          | exact resolve b2e54 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e441 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (τ X0) y) ∨ x = (M.op (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e54 X0 x
             have i₂ := b2e24 (τ X0)
             grind)
          | exact superpose b2e24 b2e54
          | (have j0 := b2e54 X0 y
             grind)
          | exact resolve b2e54 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e54
        have b2e509 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e95 x y
             have i₂ := b2e36
             grind)
          | exact superpose b2e36 b2e95
          | (have j0 := b2e95 x y
             grind)
          | exact resolve b2e95 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e514 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e509
             have r₂ := b2e22
             grind)
          | exact resolve b2e509 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e509
        have b2e518 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b2e514
             have r₂ := b2e21
             grind)
          | exact resolve b2e514 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e514
        have b2e639 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e93 x y X0
             have i₂ := b2e36
             grind)
          | exact superpose b2e36 b2e93
          | (have j0 := b2e93 x y x
             grind)
          | exact resolve b2e93 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e664 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e639 X0
             grind)
          | (have r₁ := b2e639 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e639 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e639
        have b2e668 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have j0 := b2e664 X0
             grind)
          | (have r₁ := b2e664 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e664 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e664
        have b2e5438 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 y)) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e441 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e441
          | exact resolve b2e441 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e441
        have b2e5496 : ∀ X0 : G, (σ (M.op X0 y)) = (σ (k X0 x)) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e5438 X0
             have i₂ := b2e18 X0 x
             grind)
          | exact superpose b2e18 b2e5438
          | (have j0 := b2e5438 X0
             grind)
          | exact resolve b2e5438 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5438
        have b2e5521 : ∀ X0 : G, (k X0 x) = (τ (σ (M.op X0 y))) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e13 (k X0 x)
             have i₂ := b2e5496 X0
             grind)
          | exact superpose b2e5496 b2e13
          | (have j1 := b2e5496 X0
             grind)
          | exact resolve b2e13 b2e5496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5496
        have b2e5577 : ∀ X0 : G, (M.op X0 y) = (k X0 x) ∨ (M.op X0 y) = X0 ∨ x = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e5521 X0
             have i₂ := b2e13 (M.op X0 y)
             grind)
          | exact superpose b2e13 b2e5521
          | (have j0 := b2e5521 X0
             grind)
          | exact resolve b2e5521 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5521
        have b2e5613 : (M.op (σ (M.op x y)) (σ x)) = (σ (k x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e121 x
             have i₂ := b2e5577 x
             grind)
          | exact superpose b2e5577 b2e121
          | (have j0 := b2e121 x
             have j1 := b2e5577 x
             grind)
          | exact resolve b2e121 b2e5577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121
        have b2e5657 : (M.op (σ (M.op x y)) (σ x)) = (σ (k x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
        clear b2e5613
        have b2e5659 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e5657
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5657
          | exact resolve b2e5657 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5657
        have b2e5661 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e5659
             have i₂ := b2e36
             grind)
          | exact superpose b2e36 b2e5659
          | exact resolve b2e5659 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5659
        have b2e5663 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e5661
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5661
          | exact resolve b2e5661 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5661
        have b2e6475 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e15 (σ x) (σ x)
             have i₂ := b2e5663
             grind)
          | exact superpose b2e5663 b2e15
          | (have r₁ := b2e15 (σ x) (σ x)
             have r₂ := b2e5663
             grind)
          | exact resolve b2e15 b2e5663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e6484 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ x = y := by grind
        clear b2e6475
        have b2e6486 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e6484
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e6484
          | exact resolve b2e6484 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6484
        have b2e6508 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e12 X0 (σ y) (σ x)
             have i₂ := b2e6486
             grind)
          | exact superpose b2e6486 b2e12
          | exact resolve b2e12 b2e6486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6486
        have b2e6518 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e6508 X0
             have i₂ := b2e668 X0
             grind)
          | exact superpose b2e668 b2e6508
          | exact resolve b2e6508 b2e668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6508
        have b2e6581 : ∀ X0 X1 X2 : G, (k X0 (τ (σ (M.op X1 X2)))) = (τ (σ (M.op (τ (σ X0)) X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X1 X2) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e47 X0 (σ (M.op X1 X2))
             have i₂ := b2e440 (σ X0) X1 X2
             grind)
          | exact superpose b2e440 b2e47
          | (have j1 := b2e440 (σ X0) X1 X2
             grind)
          | exact resolve b2e47 b2e440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e440
        have b2e6623 : ∀ X0 X1 X2 : G, (M.op (τ (σ X0)) X1) = (k X0 (τ (σ (M.op X1 X2)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X1 X2) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e6581 X0 X1 X2
             have i₂ := b2e13 (M.op (τ (σ X0)) X1)
             grind)
          | exact superpose b2e13 b2e6581
          | (have j0 := b2e6581 X0 X1 X2
             grind)
          | exact resolve b2e6581 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6581
        have b2e6652 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X1 X2) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e6623 X0 X1 X2
             have i₂ := b2e13 (M.op X1 X2)
             grind)
          | exact superpose b2e13 b2e6623
          | (have j0 := b2e6623 X0 X1 X2
             grind)
          | exact resolve b2e6623 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6623
        have b2e6675 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X1 X2) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e6652 X0 X1 X2
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e6652
          | (have j0 := b2e6652 X0 X1 X2
             grind)
          | exact resolve b2e6652 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6652
        have b2e6693 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e6675 X0 X1 X2
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e6675
          | (have j0 := b2e6675 X0 X1 X2
             grind)
          | exact resolve b2e6675 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6675
        have b2e6702 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e6693 X0 X1 X2
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e6693
          | (have j0 := b2e6693 X0 X1 X2
             grind)
          | exact resolve b2e6693 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6693
        have b2e6943 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e71 (σ X0)
             have i₂ := b2e143 (σ X0) X0 X0
             grind)
          | exact superpose b2e143 b2e71
          | (have j1 := b2e143 (σ X0) X0 x
             grind)
          | exact resolve b2e71 b2e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143
        have b2e6957 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e6943 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6943
        have b2e6966 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e6957 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e6957
          | (have j0 := b2e6957 X0
             grind)
          | exact resolve b2e6957 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6957
        have b2e7788 : ∀ X0 : G, (k x x) = (τ (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e6518 X0
             grind)
          | exact superpose b2e6518 b2e13
          | (have j1 := b2e6518 X0
             grind)
          | exact resolve b2e13 b2e6518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6518
        have b2e7874 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e7788 X0
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e7788
          | (have j0 := b2e7788 X0
             grind)
          | exact resolve b2e7788 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7788
        have b2e8087 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e5663
             have i₂ := b2e7874 (σ x)
             grind)
          | exact superpose b2e7874 b2e5663
          | exact resolve b2e5663 b2e7874
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5663
        have b2e8101 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by grind
        clear b2e8087
        have b2e8109 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (k x x) := by
          first
          | (have r₁ := b2e8101
             have r₂ := b2e22
             grind)
          | exact resolve b2e8101 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8101
        have b2e8565 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = y ∨ x = y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e7874 (σ y)
             have i₂ := b2e8109
             grind)
          | exact superpose b2e8109 b2e7874
          | exact resolve b2e7874 b2e8109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7874 b2e8109
        have b2e8582 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ x = (k x x) ∨ x = y := by grind
        clear b2e8565
        have b2e9630 : (τ (σ (M.op y y))) = (k (τ (σ y)) y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e60 (σ y) y
             have i₂ := b2e8582
             grind)
          | exact superpose b2e8582 b2e60
          | exact resolve b2e60 b2e8582
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60 b2e8582
        have b2e9643 : (τ (σ (M.op y y))) = (k (τ (σ y)) y) ∨ (σ y) = (σ (M.op y y)) ∨ x = (k x x) ∨ x = y := by grind
        clear b2e9630
        have b2e9655 : (τ (σ (M.op y y))) = (k (τ (σ y)) y) ∨ x = (k x x) ∨ x = y := by
          first
          | (have r₁ := b2e9643
             have r₂ := b2e518
             grind)
          | exact resolve b2e9643 b2e518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9643
        have b2e9668 : (τ (σ (M.op y y))) = (k y y) ∨ x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e9655
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e9655
          | exact resolve b2e9655 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9655
        have b2e9677 : x = (k x x) ∨ (M.op y y) = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e9668
             have i₂ := b2e13 (M.op y y)
             grind)
          | exact superpose b2e13 b2e9668
          | exact resolve b2e9668 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9668
        have b2e9742 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y y) = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e5577 x
             have i₂ := b2e9677
             grind)
          | exact superpose b2e9677 b2e5577
          | (have j0 := b2e5577 x
             grind)
          | exact resolve b2e5577 b2e9677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9677
        have b2e9775 : x = (M.op x y) ∨ (M.op y y) = (k y y) ∨ x = y := by grind
        clear b2e9742
        have b2e9786 : x = y ∨ (M.op y y) = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e9775
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e9775
          | exact resolve b2e9775 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9775
        have b2e9787 : (M.op y y) = (k y y) ∨ x = y := by grind
        clear b2e9786
        have b2e9855 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e93 y y X0
             have i₂ := b2e9787
             grind)
          | exact superpose b2e9787 b2e93
          | (have j0 := b2e93 y y x
             grind)
          | exact resolve b2e93 b2e9787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e9867 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e9855 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9855
        have b2e9870 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e9867 X0
             have i₂ := b2e668 X0
             grind)
          | exact superpose b2e668 b2e9867
          | exact resolve b2e9867 b2e668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e668 b2e9867
        have b2e13131 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e15 (σ y) (σ y)
             have i₂ := b2e9870 X0
             grind)
          | exact superpose b2e9870 b2e15
          | (have j1 := b2e9870 X0
             grind)
          | (have r₁ := b2e15 (σ y) (σ y)
             have r₂ := b2e9870 X0
             grind)
          | exact resolve b2e15 b2e9870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9870
        have b2e13142 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e13131 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13131
        have b2e13169 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e13142 X0
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e13142
          | (have j0 := b2e13142 X0
             grind)
          | exact resolve b2e13142 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13142
        have b2e13405 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e13169 X0
             have i₂ := b2e9787
             grind)
          | exact superpose b2e9787 b2e13169
          | (have j0 := b2e13169 X0
             grind)
          | exact resolve b2e13169 b2e9787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9787 b2e13169
        have b2e13544 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e13405 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13405
        have b2e13585 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e13544 X0
             grind)
          | (have r₁ := b2e13544 X0
             have r₂ := b2e518
             grind)
          | exact resolve b2e13544 b2e518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13544
        have b2e13876 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
          first
          | (have i₁ := b2e71 (σ x)
             have i₂ := b2e13585 (σ x)
             grind)
          | exact superpose b2e13585 b2e71
          | exact resolve b2e71 b2e13585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e58877 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k x (k x (τ (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e181 x (σ y) x
             have i₂ := b2e13876
             grind)
          | exact superpose b2e13876 b2e181
          | (have j0 := b2e181 x (σ y) x
             grind)
          | exact resolve b2e181 b2e13876
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181 b2e13876
        have b2e58948 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k x (k x (τ (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have r₁ := b2e58877
             have r₂ := b2e22
             grind)
          | exact resolve b2e58877 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58877
        have b2e58967 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k x (k x (τ (σ y))))) ∨ x = y := by
          first
          | (have r₁ := b2e58948
             have r₂ := b2e21
             grind)
          | exact resolve b2e58948 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58948
        have b2e58982 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k x (k x y))) ∨ x = y := by
          first
          | (have i₁ := b2e58967
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e58967
          | exact resolve b2e58967 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58967
        have b2e58993 : (σ (k x (M.op y y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e58982
             have i₂ := b2e36
             grind)
          | exact superpose b2e36 b2e58982
          | exact resolve b2e58982 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58982
        have b2e93953 : (σ (k x (k x x))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e6966 x
             have i₂ := b2e13585 (σ x)
             grind)
          | exact superpose b2e13585 b2e6966
          | exact resolve b2e6966 b2e13585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6966 b2e13585
        have b2e93980 : (σ (k x (k x x))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
          first
          | (have r₁ := b2e93953
             have r₂ := b2e22
             grind)
          | exact resolve b2e93953 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93953
        have b2e100565 : (σ (k x (k x x))) = (σ (k x (M.op y y))) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e58993
             have i₂ := b2e93980
             grind)
          | exact superpose b2e93980 b2e58993
          | exact resolve b2e58993 b2e93980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58993 b2e93980
        have b2e100588 : (σ (k x (k x x))) = (σ (k x (M.op y y))) ∨ x = y := by grind
        clear b2e100565
        have b2e100710 : (k x (k x x)) = (τ (σ (k x (M.op y y)))) ∨ x = y := by
          first
          | (have i₁ := b2e13 (k x (k x x))
             have i₂ := b2e100588
             grind)
          | exact superpose b2e100588 b2e13
          | exact resolve b2e13 b2e100588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100588
        have b2e100754 : (k x (M.op y y)) = (k x (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e100710
             have i₂ := b2e13 (k x (M.op y y))
             grind)
          | exact superpose b2e13 b2e100710
          | exact resolve b2e100710 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100710
        have b2e100794 : (k x (M.op x y)) = (k x (M.op y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e100754
             have i₂ := b2e5577 x
             grind)
          | exact superpose b2e5577 b2e100754
          | (have j1 := b2e5577 x
             grind)
          | exact resolve b2e100754 b2e5577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5577 b2e100754
        have b2e100813 : (k x (M.op x y)) = (k x (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by grind
        clear b2e100794
        have b2e100825 : (k x y) = (k x (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e100813
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e100813
          | exact resolve b2e100813 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100813
        have b2e100835 : (M.op y y) = (k x (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e100825
             have i₂ := b2e36
             grind)
          | exact superpose b2e36 b2e100825
          | exact resolve b2e100825 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e100825
        have b2e100846 : x = y ∨ (M.op y y) = (k x (M.op y y)) ∨ x = y := by
          first
          | (have i₁ := b2e100835
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e100835
          | exact resolve b2e100835 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100835
        have b2e100847 : (M.op y y) = (k x (M.op y y)) ∨ x = y := by grind
        clear b2e100846
        have b2e100885 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e6702 x y y
             have i₂ := b2e100847
             grind)
          | exact superpose b2e100847 b2e6702
          | (have j0 := b2e6702 x y y
             grind)
          | exact resolve b2e6702 b2e100847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6702 b2e100847
        have b2e100896 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by grind
        clear b2e100885
        have b2e100919 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b2e100896
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e100896
          | exact resolve b2e100896 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100896
        have b2e100934 : x = y ∨ y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e100919
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e100919
          | exact resolve b2e100919 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100919
        have b2e100935 : y = (M.op y y) ∨ x = y := by grind
        clear b2e100934
        have b2e100985 : (σ y) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e518
             have i₂ := b2e100935
             grind)
          | exact superpose b2e100935 b2e518
          | exact resolve b2e518 b2e100935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100935
        have b2e101125 : x = y := by grind
        clear b2e100985
        have b2e101146 : y = (M.op y y) := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e101125
             grind)
          | exact superpose b2e101125 b2e20
          | exact resolve b2e20 b2e101125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e101125
        have b2e101187 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e518
             have i₂ := b2e101146
             grind)
          | exact superpose b2e101146 b2e518
          | exact resolve b2e518 b2e101146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e518 b2e101146
        have b2e101280 : False := by grind
        exact b2e101280
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
        have b3e26 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X0 (M.op X1 X2)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b3e15 X0 (M.op X0 X0)
             have r₂ := b3e12 X0 X0 X0
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e33 X0 X1 X2
             have i₂ := b3e12 (M.op X1 X2) X1 X2
             grind)
          | exact superpose b3e12 b3e33
          | (have j0 := b3e33 X0 X1 X2
             grind)
          | (have r₁ := b3e33 X0 X0 (M.op X0 X2)
             have r₂ := b3e12 X0 X0 X2
             grind)
          | (have r₁ := b3e33 (M.op X1 X2) (M.op X1 X2) X1
             have r₂ := b3e12 (M.op X1 X2) X1 X2
             grind)
          | exact resolve b3e33 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e90 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b3e37 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e126 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e51 X0 x
             have i₂ := b3e26 (σ X0)
             grind)
          | exact superpose b3e26 b3e51
          | (have j0 := b3e51 X0 y
             grind)
          | exact resolve b3e51 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e51
        have b3e1074 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e126 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e126
          | exact resolve b3e126 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e126
        have b3e1102 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e1074
        have b3e1111 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b3e1102
             have r₂ := b3e25
             grind)
          | exact resolve b3e1102 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e1102
        have b3e1130 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e1111
             grind)
          | exact superpose b3e1111 b3e13
          | exact resolve b3e13 b3e1111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1111
        have b3e1165 : y = (k x x) := by
          first
          | (have i₁ := b3e1130
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1130
          | exact resolve b3e1130 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1130
        have b3e1195 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e1165
             grind)
          | exact superpose b3e1165 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e1165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1196 : x = (M.op x x) ∨ y = (M.op x x) := by grind
        clear b3e1195
        have b3e1281 : (M.op x x) = (k x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b3e90 x
             have i₂ := b3e1196
             grind)
          | exact superpose b3e1196 b3e90
          | exact resolve b3e90 b3e1196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90 b3e1196
        have b3e1293 : y = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b3e1281
             have i₂ := b3e1165
             grind)
          | exact superpose b3e1165 b3e1281
          | exact resolve b3e1281 b3e1165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1165 b3e1281
        have b3e1294 : y = (M.op x x) := by grind
        clear b3e1293
        have b3e1381 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e1294
             grind)
          | exact superpose b3e1294 b3e12
          | exact resolve b3e12 b3e1294
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1497 : y = (M.op x y) := by
          first
          | (have i₁ := b3e1294
             have i₂ := b3e1381 x
             grind)
          | exact superpose b3e1381 b3e1294
          | exact resolve b3e1294 b3e1381
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1294 b3e1381
        have b3e1592 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1497
             grind)
          | exact superpose b3e1497 b3e21
          | exact resolve b3e21 b3e1497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1497
        have b3e1603 : False := by grind
        exact b3e1603
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
          have b5e45 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e47 : x = y ∨ y = (k x y) := by grind
          clear b5e45
          have b5e48 : y = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e25
               grind)
            | exact resolve b5e47 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e47
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e114 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e429 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e114 x y
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e114
            | (have j0 := b5e114 x y
               grind)
            | exact resolve b5e114 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e114
          have b5e434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e429
          have b5e437 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e434
               have r₂ := b5e24
               grind)
            | exact resolve b5e434 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e434
          have b5e441 : False := by grind
          exact b5e441
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
        have b6e29 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e31 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ x)
             have i₂ := b6e24 X0
             grind)
          | exact superpose b6e24 b6e15
          | (have j0 := b6e15 X0 (σ x)
             grind)
          | exact resolve b6e15 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e29
        have b6e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e24 (σ x)
             grind)
          | exact superpose b6e24 b6e31
          | (have j0 := b6e31 X0
             grind)
          | exact resolve b6e31 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e35 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e32
          | exact resolve b6e32 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e36 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e33 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e33
          | (have j0 := b6e33 X0
             grind)
          | exact resolve b6e33 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e56 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e15
          | exact resolve b6e15 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e56
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e56
          | exact resolve b6e56 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e104 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52 y y
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e52
          | exact resolve b6e52 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e105 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e52 X0 x
             have i₂ := b6e24 (σ X0)
             grind)
          | exact superpose b6e24 b6e52
          | (have j0 := b6e52 X0 y
             grind)
          | exact resolve b6e52 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e52
        have b6e118 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
        clear b6e104
        have b6e123 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have r₁ := b6e118
             have r₂ := b6e58
             grind)
          | exact resolve b6e118 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e118
        have b6e130 : (k x y) = (τ (σ (k y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e123
             grind)
          | exact superpose b6e123 b6e13
          | exact resolve b6e13 b6e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e141 : (k x y) = (k y y) := by
          first
          | (have i₁ := b6e130
             have i₂ := b6e13 (k y y)
             grind)
          | exact superpose b6e13 b6e130
          | exact resolve b6e130 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130
        have b6e184 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e141
             grind)
          | exact superpose b6e141 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e185 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e184
             have r₂ := b6e21
             grind)
          | exact resolve b6e184 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184
        have b6e188 : (M.op x y) = (k y y) := by
          first
          | (have r₁ := b6e185
             have r₂ := b6e20
             grind)
          | exact resolve b6e185 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e185
        have b6e214 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e188
             grind)
          | exact superpose b6e188 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e215 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b6e214
        have b6e217 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e36 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e36
          | (have j0 := b6e36 (σ x)
             grind)
          | exact resolve b6e36 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e222 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b6e217
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e217
          | exact resolve b6e217 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217
        have b6e405 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y y)) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e215
             grind)
          | exact superpose b6e215 b6e12
          | exact resolve b6e12 b6e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e215
        have b6e407 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e405 X0
             have i₂ := b6e12 X0 y y
             grind)
          | exact superpose b6e12 b6e405
          | exact resolve b6e405 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e405
        have b6e435 : ∀ X0 : G, y ≠ y ∨ y = (k y y) ∨ (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e15 y y
             have i₂ := b6e407 X0
             grind)
          | exact superpose b6e407 b6e15
          | (have j1 := b6e407 X0
             grind)
          | (have r₁ := b6e15 y y
             have r₂ := b6e407 X0
             grind)
          | exact resolve b6e15 b6e407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e407
        have b6e436 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e435 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e435
        have b6e438 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e436 X0
             have i₂ := b6e188
             grind)
          | exact superpose b6e188 b6e436
          | (have j0 := b6e436 X0
             grind)
          | exact resolve b6e436 b6e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e188 b6e436
        have b6e440 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e438 X0
             grind)
          | (have r₁ := b6e438 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e438 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e438
        have b6e1218 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e105 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e105
          | exact resolve b6e105 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e1246 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1218
        have b6e1259 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e1246
             have r₂ := b6e222
             grind)
          | exact resolve b6e1246 b6e222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e222 b6e1246
        have b6e1316 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e1259
             have i₂ := b6e17 x x
             grind)
          | exact superpose b6e17 b6e1259
          | (have j1 := b6e17 x x
             grind)
          | exact resolve b6e1259 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1259
        have b6e1338 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b6e1316
        have b6e1356 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e1338
             have i₂ := b6e440 x
             grind)
          | exact superpose b6e440 b6e1338
          | exact resolve b6e1338 b6e440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1338
        have b6e1360 : x = (M.op x x) := by
          first
          | (have r₁ := b6e1356
             have r₂ := b6e23
             grind)
          | exact resolve b6e1356 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e1356
        have b6e1362 : x = (M.op x y) := by
          first
          | (have i₁ := b6e1360
             have i₂ := b6e440 x
             grind)
          | exact superpose b6e440 b6e1360
          | exact resolve b6e1360 b6e440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e440 b6e1360
        have b6e1364 : False := by grind
        exact b6e1364
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
          have b7e37 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e39 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e40 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e39
               have r₂ := b7e25
               grind)
            | exact resolve b7e39 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e39
          have b7e41 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e40
            | exact resolve b7e40 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e14
            | exact resolve b7e14 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : y = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e56 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e55
          have b7e58 : x = (M.op x y) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e21
               grind)
            | exact resolve b7e56 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : False := by grind
          exact b7e60
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
          have b8e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e92 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e20
            | (have j1 := b8e44 x y
               grind)
            | exact resolve b8e20 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e104 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e92
               have r₂ := b8e24
               grind)
            | exact resolve b8e92 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e108 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e104
               have r₂ := b8e23
               grind)
            | exact resolve b8e104 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e109 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e108
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e108
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e108 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e110 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e109
          have b8e111 : y = (M.op x y) := by
            first
            | (have r₁ := b8e110
               have r₂ := b8e22
               grind)
            | exact resolve b8e110 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e112 : False := by grind
          exact b8e112
