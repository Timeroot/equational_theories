import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1486 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
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
          have b5e46 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e49 : x = y ∨ x = (k x y) := by grind
          clear b5e46
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
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e151 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e902 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e151 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e151
            | (have j0 := b5e151 x y
               grind)
            | exact resolve b5e151 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e151
          have b5e905 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e902
          have b5e908 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e905
               have r₂ := b5e24
               grind)
            | exact resolve b5e905 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e905
          have b5e912 : False := by grind
          exact b5e912
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
          have b7e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e47 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e58 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e48
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e48 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e26
               grind)
            | exact resolve b7e58 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e58
          have b7e60 : x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e22
               grind)
            | exact resolve b7e59 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e61 : False := by grind
          exact b7e61
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
          have b8e115 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e122 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e115
               have r₂ := b8e24
               grind)
            | exact resolve b8e115 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e128 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e122
               have r₂ := b8e23
               grind)
            | exact resolve b8e122 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e128
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e128
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e128
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e128
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e128 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e132 : x = (M.op x y) ∨ x = y := by grind
          clear b8e131
          have b8e133 : x = y := by
            first
            | (have r₁ := b8e132
               have r₂ := b8e22
               grind)
            | exact resolve b8e132 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e134 : False := by grind
          exact b8e134

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1489 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1489 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
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
      have b0e76 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e76 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e117 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e77 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e77
        | exact resolve b0e77 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e77 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e77
        | exact resolve b0e77 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e121 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e117
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e117
        | exact resolve b0e117 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e121
           have i₂ := b0e118
           grind)
        | exact superpose b0e118 b0e121
        | exact resolve b0e121 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118 b0e121
      have b0e123 : False := by grind
      exact b0e123
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
        have b1e37 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e39 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e37
          | exact resolve b1e37 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e73 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e74 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e73 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e103 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e19
          | exact resolve b1e19 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e137 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e74 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e74
          | exact resolve b1e74 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e144 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e103
             have i₂ := b1e137
             grind)
          | exact superpose b1e137 b1e103
          | exact resolve b1e103 b1e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103 b1e137
        have b1e146 : False := by grind
        exact b1e146
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e66 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e67 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e66 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e279 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e67 X0
             have i₂ := b2e49 X0 X1
             grind)
          | (have i₁ := b2e67 X0
             have i₂ := b2e49 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e49 b2e67
          | (have j1 := b2e49 X1 X0
             grind)
          | exact resolve b2e67 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e67
        have b2e296 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e279 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e279
        have b2e1080 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e296 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e296
        have b2e1081 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e1080 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1080
        have b2e1274 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e1081 (σ X0)
             grind)
          | exact superpose b2e1081 b2e18
          | exact resolve b2e18 b2e1081
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1282 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1274 X0
             have i₂ := b2e1081 X0
             grind)
          | exact superpose b2e1081 b2e1274
          | exact resolve b2e1274 b2e1081
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1081 b2e1274
        have b2e1685 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1282 x
             grind)
          | exact superpose b2e1282 b2e21
          | exact resolve b2e21 b2e1282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1282
        have b2e1723 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1685
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1685
          | exact resolve b2e1685 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1685
        have b2e1724 : False := by grind
        exact b2e1724
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
        have b3e38 : (M.op x y) = (k y x) := by grind
        have b3e63 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e76 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e63
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e63
          | exact resolve b3e63 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e77 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e76
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e76
          | exact resolve b3e76 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e78 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e77
             have r₂ := b3e19
             grind)
          | exact resolve b3e77 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e88 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e78
        have b3e89 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e88
          | exact resolve b3e88 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e92 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e89
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e89
          | exact resolve b3e89 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e89
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
          have b4e43 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e44 : (M.op x y) = (k y x) := by grind
          have b4e46 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e43
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e43
            | exact resolve b4e43 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e47 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e46
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e46
            | exact resolve b4e46 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e46
          have b4e48 : False := by grind
          exact b4e48
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b5e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e74 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e75 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e74 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74
          have b5e275 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e75 X0
               have i₂ := b5e56 X0 X1
               grind)
            | (have i₁ := b5e75 X0
               have i₂ := b5e56 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e56 b5e75
            | (have j1 := b5e56 X1 X0
               grind)
            | exact resolve b5e75 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e75
          have b5e290 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e275 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e275
          have b5e1061 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e290 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e290
          have b5e1062 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e1061 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1061
          have b5e1249 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e1062 (σ X0)
               grind)
            | exact superpose b5e1062 b5e19
            | exact resolve b5e19 b5e1062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1257 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1249 X0
               have i₂ := b5e1062 X0
               grind)
            | exact superpose b5e1062 b5e1249
            | exact resolve b5e1249 b5e1062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1062 b5e1249
          have b5e1655 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1257 y
               grind)
            | exact superpose b5e1257 b5e24
            | exact resolve b5e24 b5e1257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1257
          have b5e1692 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1655
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1655
            | exact resolve b5e1655 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1655
          have b5e1693 : False := by grind
          exact b5e1693
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
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e35 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e36 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e100 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e81 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e81
          | exact resolve b6e81 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e106 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e100
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e100
          | exact resolve b6e100 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100
        have b6e162 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e106
             grind)
          | exact superpose b6e106 b6e19
          | exact resolve b6e19 b6e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e193 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e81 X0
             have i₂ := b6e51 X0 X1
             grind)
          | (have i₁ := b6e81 X0
             have i₂ := b6e51 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e51 b6e81
          | (have j1 := b6e51 X1 X0
             grind)
          | exact resolve b6e81 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e81
        have b6e204 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e193 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e193
        have b6e312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e162
             have i₂ := b6e56 x y
             grind)
          | exact superpose b6e56 b6e162
          | (have j1 := b6e56 x y
             grind)
          | exact resolve b6e162 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56 b6e162
        have b6e341 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b6e312
        have b6e349 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e341
             have r₂ := b6e20
             grind)
          | exact resolve b6e341 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e341
        have b6e785 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e59 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e59
          | exact resolve b6e59 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e956 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e785
        have b6e1007 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e956
             grind)
          | exact superpose b6e956 b6e13
          | exact resolve b6e13 b6e956
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e956
        have b6e1021 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1007
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1007
          | exact resolve b6e1007 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1007
        have b6e1544 : y = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e204 x x
             have i₂ := b6e1021
             grind)
          | exact superpose b6e1021 b6e204
          | exact resolve b6e204 b6e1021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204 b6e1021
        have b6e1577 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1544
        have b6e1590 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1577
             have r₂ := b6e20
             grind)
          | exact resolve b6e1577 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1577
        have b6e1592 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1590
             grind)
          | exact superpose b6e1590 b6e19
          | exact resolve b6e19 b6e1590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1595 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e1590
             grind)
          | exact superpose b6e1590 b6e36
          | exact resolve b6e36 b6e1590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e1600 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1590
             grind)
          | exact superpose b6e1590 b6e13
          | exact resolve b6e13 b6e1590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1617 : x = y := by
          first
          | (have i₁ := b6e1600
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1600
          | exact resolve b6e1600 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1600
        have b6e1620 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e1595
             have i₂ := b6e349
             grind)
          | exact superpose b6e349 b6e1595
          | exact resolve b6e1595 b6e349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e349 b6e1595
        have b6e1623 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e1592
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1592
          | exact resolve b6e1592 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1592
        have b6e1629 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b6e1620
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1620
          | exact resolve b6e1620 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1620
        have b6e1632 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e1623
             have i₂ := b6e1590
             grind)
          | exact superpose b6e1590 b6e1623
          | exact resolve b6e1623 b6e1590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1623
        have b6e1638 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b6e1629
             have i₂ := b6e1590
             grind)
          | exact superpose b6e1590 b6e1629
          | exact resolve b6e1629 b6e1590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1590 b6e1629
        have b6e1639 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e1632
             have i₂ := b6e1617
             grind)
          | exact superpose b6e1617 b6e1632
          | exact resolve b6e1632 b6e1617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1632
        have b6e1640 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e1638
             have i₂ := b6e1617
             grind)
          | exact superpose b6e1617 b6e1638
          | exact resolve b6e1638 b6e1617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1617 b6e1638
        have b6e1641 : False := by grind
        exact b6e1641
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
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e89 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e87 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e342 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e89 X0
               have i₂ := b7e67 X0 X1
               grind)
            | (have i₁ := b7e89 X0
               have i₂ := b7e67 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e67 b7e89
            | (have j1 := b7e67 X1 X0
               grind)
            | exact resolve b7e89 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e89
          have b7e358 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e342 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e342
          have b7e668 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e358 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e358
          have b7e669 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e668 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e668
          have b7e768 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e669 (σ X0)
               grind)
            | exact superpose b7e669 b7e19
            | exact resolve b7e19 b7e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e775 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e768 X0
               have i₂ := b7e669 X0
               grind)
            | exact superpose b7e669 b7e768
            | exact resolve b7e768 b7e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e669 b7e768
          have b7e1393 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e775 y
               grind)
            | exact superpose b7e775 b7e24
            | exact resolve b7e24 b7e775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e775
          have b7e1812 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e1393
               grind)
            | exact superpose b7e1393 b7e14
            | exact resolve b7e14 b7e1393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1393
          have b7e1831 : x = (M.op y y) := by
            first
            | (have i₁ := b7e1812
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1812
            | exact resolve b7e1812 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1812
          have b7e1836 : False := by grind
          exact b7e1836
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
          have b8e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e229 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e230 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e229
               have r₂ := b8e24
               grind)
            | exact resolve b8e229 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e229
          have b8e231 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e230
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e230
            | exact resolve b8e230 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e230
          have b8e232 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e231
               grind)
            | exact superpose b8e231 b8e20
            | exact resolve b8e20 b8e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231
          have b8e241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e232
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e232
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e232 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e232
          have b8e242 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e241
          have b8e243 : x = (M.op y y) := by
            first
            | (have r₁ := b8e242
               have r₂ := b8e21
               grind)
            | exact resolve b8e242 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e242
          have b8e245 : False := by grind
          exact b8e245

/-- `Equation1516`: `x = (y ◇ y) ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1516 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1516 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1516.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
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
      have b0e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b0e189 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e55 x
           grind)
        | exact superpose b0e55 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e55 x
           grind)
        | exact resolve b0e22 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e55
      have b0e200 : False := by grind
      exact b0e200
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e51 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b1e53 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
        have b1e56 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e53
        have b1e57 : (M.op y y) = (k x y) := by grind
        clear b1e51
        have b1e58 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
        have b1e59 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
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
        have b1e74 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e77 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e138 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e23
          | exact resolve b1e23 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e853 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e77 (σ x)
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e77
          | (have j0 := b1e77 (σ x)
             grind)
          | (have r₁ := b1e77 (σ x)
             have r₂ := b1e59
             grind)
          | exact resolve b1e77 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e77
        have b1e854 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e853
        have b1e855 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e854
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e854
          | exact resolve b1e854 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e854
        have b1e856 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e855
             have r₂ := b1e138
             grind)
          | exact resolve b1e855 b1e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e855
        have b1e857 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e856
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e856
          | exact resolve b1e856 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e856
        have b1e858 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e857
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e857
          | exact resolve b1e857 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e857
        have b1e859 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e858
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e858
          | exact resolve b1e858 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e858
        have b1e860 : False := by grind
        exact b1e860
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b2e52 : (M.op y y) = (k x y) := by grind
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
        have b2e91 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e147 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
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
        have b2e1524 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e91 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e1525 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1524
             have r₂ := b2e21
             grind)
          | exact resolve b2e1524 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1524
        have b2e1526 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1525
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1525
          | exact resolve b2e1525 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1525
        have b2e1527 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1526
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e1526
          | exact resolve b2e1526 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e1526
        have b2e1528 : False := by grind
        exact b2e1528
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b3e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e56 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
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
        have b3e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e55 (σ X0)
             grind)
          | exact superpose b3e55 b3e18
          | exact resolve b3e18 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e61 X0
             have i₂ := b3e55 X0
             grind)
          | exact superpose b3e55 b3e61
          | exact resolve b3e61 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e74 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e15
          | exact resolve b3e15 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e82 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e80
        have b3e83 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e82
          | exact resolve b3e82 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e84 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e83
             have i₂ := b3e55 y
             grind)
          | exact superpose b3e55 b3e83
          | exact resolve b3e83 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e83
        have b3e85 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e84
          | exact resolve b3e84 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e191 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e68 x
             grind)
          | exact superpose b3e68 b3e23
          | exact resolve b3e23 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e68
        have b3e330 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e74 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e331 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e330
             have r₂ := b3e20
             grind)
          | exact resolve b3e330 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e330
        have b3e335 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e331
             grind)
          | exact superpose b3e331 b3e85
          | exact resolve b3e85 b3e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85 b3e331
        have b3e339 : False := by grind
        exact b3e339
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
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
          have b4e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e67
          have b4e73 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
          have b4e75 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e70 y
               grind)
            | exact superpose b4e70 b4e73
            | exact resolve b4e73 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e73
          have b4e76 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
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
          have b4e77 : False := by grind
          exact b4e77
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e87 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e126 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e376 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e87 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e377 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e376
               have r₂ := b5e21
               grind)
            | exact resolve b5e376 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e376
          have b5e1841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e126 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e126
          have b5e1842 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1841
               have r₂ := b5e23
               grind)
            | exact resolve b5e1841 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1841
          have b5e1843 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1842
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1842
            | exact resolve b5e1842 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1842
          have b5e1844 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1843
               have i₂ := b5e377
               grind)
            | exact superpose b5e377 b5e1843
            | exact resolve b5e1843 b5e377
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e377 b5e1843
          have b5e1847 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1844
               grind)
            | exact superpose b5e1844 b5e23
            | exact resolve b5e23 b5e1844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1844
          have b5e1866 : False := by grind
          exact b5e1866
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e52 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
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
        have b6e73 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
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
        have b6e75 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e73
        have b6e76 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e75
          | exact resolve b6e75 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e77 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e76
             have i₂ := b6e51 y
             grind)
          | exact superpose b6e51 b6e76
          | exact resolve b6e76 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e76
        have b6e139 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e77
             grind)
          | exact superpose b6e77 b6e13
          | exact resolve b6e13 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e140 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e139
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e139
          | exact resolve b6e139 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e176 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e140
             grind)
          | exact superpose b6e140 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e140
        have b6e177 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e176
        have b6e179 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e177
             have r₂ := b6e21
             grind)
          | exact resolve b6e177 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e177
        have b6e181 : False := by grind
        exact b6e181
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          have b7e67 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e64
          have b7e68 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
          have b7e69 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
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
          have b7e88 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e92 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e23
            | exact resolve b7e23 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e98 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e92
            | exact resolve b7e92 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e139 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e110 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e840 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e91 (σ x)
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e91
            | (have j0 := b7e91 (σ x)
               grind)
            | (have r₁ := b7e91 (σ x)
               have r₂ := b7e69
               grind)
            | exact resolve b7e91 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e91
          have b7e841 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e840
          have b7e842 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e841
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e841
            | exact resolve b7e841 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e841
          have b7e843 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e842
               have r₂ := b7e98
               grind)
            | exact resolve b7e842 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e842
          have b7e844 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e843
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e843
            | exact resolve b7e843 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e843
          have b7e845 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e844
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e844
            | exact resolve b7e844 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e844
          have b7e847 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e845
               have i₂ := b7e139 x y
               grind)
            | exact superpose b7e139 b7e845
            | (have j1 := b7e139 x y
               grind)
            | exact resolve b7e845 b7e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e849 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e845
               grind)
            | exact superpose b7e845 b7e14
            | exact resolve b7e14 b7e845
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e845
          have b7e869 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e849
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e849
            | exact resolve b7e849 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e849
          have b7e871 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e847
               have r₂ := b7e98
               grind)
            | exact resolve b7e847 b7e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e847
          have b7e874 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e871
               have r₂ := b7e22
               grind)
            | exact resolve b7e871 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e871
          have b7e875 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e874
               have i₂ := b7e869
               grind)
            | exact superpose b7e869 b7e874
            | exact resolve b7e874 b7e869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e869 b7e874
          have b7e876 : False := by grind
          exact b7e876
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e118 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1541 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e118 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e1542 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1541
               have r₂ := b8e23
               grind)
            | exact resolve b8e1541 b8e23
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
          have b8e1548 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
          have b8e1634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1548
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1548
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1548 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1548
          have b8e1635 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1634
          have b8e1637 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1635
               have r₂ := b8e21
               grind)
            | exact resolve b8e1635 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1635
          have b8e1640 : False := by grind
          exact b8e1640

/-- `Equation1516`: `x = (y ◇ y) ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation1516 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1516 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1516.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e42 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e44 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e46 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e44
      have b0e47 : (M.op x x) = (k x y) := by grind
      clear b0e42
      have b0e48 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e46
        | exact resolve b0e46 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e49 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e48
        | exact resolve b0e48 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e48
      have b0e50 : False := by grind
      exact b0e50
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
        have b2e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : (M.op x x) = (k x y) := by grind
        clear b2e50
        have b2e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e52 (σ X0)
             grind)
          | exact superpose b2e52 b2e18
          | exact resolve b2e18 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e55 X0
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e55
          | exact resolve b2e55 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e55
        have b2e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0 X1
             have i₂ := b2e62 X0
             grind)
          | exact superpose b2e62 b2e71
          | (have j0 := b2e71 X0 X1
             grind)
          | exact resolve b2e71 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e472 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e86 x y
             grind)
          | exact superpose b2e86 b2e21
          | (have j1 := b2e86 x y
             grind)
          | exact resolve b2e21 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e518 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e472
             have r₂ := b2e24
             grind)
          | exact resolve b2e472 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e472
        have b2e531 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e518
             have r₂ := b2e22
             grind)
          | exact resolve b2e518 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e518
        have b2e537 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e531
             have i₂ := b2e53
             grind)
          | exact superpose b2e53 b2e531
          | exact resolve b2e531 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e531
        have b2e539 : False := by grind
        exact b2e539
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
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
        have b6e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e53 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e51
        have b6e54 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e53
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e53
          | exact resolve b6e53 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e91 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e24
          | exact resolve b6e24 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e54
        have b6e119 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e91
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e91
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e91
             have r₂ := b6e17 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e91
             have r₂ := b6e17 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e91 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e120 : (M.op x y) = (M.op x x) ∨ x = y := by grind
        clear b6e119
        have b6e121 : x = y := by
          first
          | (have r₁ := b6e120
             have r₂ := b6e20
             grind)
          | exact resolve b6e120 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e122 : False := by grind
        exact b6e122
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
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
          have b8e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e43 (σ X0)
               grind)
            | exact superpose b8e43 b8e19
            | exact resolve b8e19 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e45 X0
               have i₂ := b8e43 X0
               grind)
            | exact superpose b8e43 b8e45
            | exact resolve b8e45 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43 b8e45
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
          have b8e60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
               have r₂ := b8e18 (M.op X0 X1) (M.op X0 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57 X0 X1
               have i₂ := b8e50 X0
               grind)
            | exact superpose b8e50 b8e57
            | (have j0 := b8e57 X0 X1
               grind)
            | exact resolve b8e57 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e105 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e108 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e105 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e105 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e105 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e105 X0 X1
               have r₂ := b8e18 (M.op X0 X1) (M.op X0 X0)
               grind)
            | exact resolve b8e105 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e215 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e108 (τ X0) X1
               grind)
            | exact superpose b8e108 b8e26
            | (have j1 := b8e108 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e108
          have b8e411 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 x y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e456 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e411
               have r₂ := b8e24
               grind)
            | exact resolve b8e411 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e411
          have b8e824 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e215 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e215
            | exact resolve b8e215 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e215
          have b8e855 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e824 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e824
            | (have j0 := b8e824 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e824 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e824
          have b8e1264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e456
               have i₂ := b8e855 x y
               grind)
            | exact superpose b8e855 b8e456
            | (have j1 := b8e855 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b8e456
               have r₂ := b8e855 x y
               grind)
            | (have r₁ := b8e456
               have r₂ := b8e855 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e456
               have r₂ := b8e855 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e456 b8e855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e456 b8e855
          have b8e1265 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b8e1264
          have b8e1271 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1265
               have r₂ := b8e22
               grind)
            | exact resolve b8e1265 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1265
          have b8e1278 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e1271
               grind)
            | exact superpose b8e1271 b8e23
            | exact resolve b8e23 b8e1271
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1271
          have b8e1300 : False := by grind
          exact b8e1300

/-- `Equation1516`: `x = (y ◇ y) ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1516 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1516 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1516.models_iff G M).mp hM
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b5e44 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e47 : x = y ∨ x = (k x y) := by grind
          clear b5e44
          have b5e48 : x = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e21
               grind)
            | exact resolve b5e47 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e150 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e741 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e150 x y
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e150
            | (have j0 := b5e150 x y
               grind)
            | exact resolve b5e150 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e150
          have b5e744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e741
          have b5e747 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e744
               have r₂ := b5e24
               grind)
            | exact resolve b5e744 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e744
          have b5e751 : False := by grind
          exact b5e751
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e121 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e112
               have r₂ := b8e24
               grind)
            | exact resolve b8e112 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e126 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e121
               have r₂ := b8e23
               grind)
            | exact resolve b8e121 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e129 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e126
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e126
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e126
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e126
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e126 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e126
          have b8e130 : x = (M.op x y) ∨ x = y := by grind
          clear b8e129
          have b8e131 : x = y := by
            first
            | (have r₁ := b8e130
               have r₂ := b8e22
               grind)
            | exact resolve b8e130 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e132 : False := by grind
          exact b8e132

/-- `Equation1526`: `x = (y ◇ y) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation1526 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1526 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1526.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : y = (M.op (M.op x x) (M.op x (M.op x x))) := by
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e26 : x = y := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e11 x x
           grind)
        | exact superpose b0e11 b0e23
        | exact resolve b0e23 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e26
           grind)
        | exact superpose b0e26 b0e18
        | exact resolve b0e18 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e35
      have b0e39 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e37
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e37
        | exact resolve b0e37 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e41 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e26
           grind)
        | exact superpose b0e26 b0e39
        | exact resolve b0e39 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e39
      have b0e42 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e41
        | exact resolve b0e41 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e41
      have b0e43 : False := by grind
      exact b0e43
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : y = (M.op (M.op x x) (M.op x (M.op x x))) := by
          first
          | (have i₁ := b1e12 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : x = y := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e12 x x
             grind)
          | exact superpose b1e12 b1e25
          | exact resolve b1e25 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e30 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e21
          | exact resolve b1e21 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e31 : False := by grind
        exact b1e31
      · have b2e12 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : y = (M.op (M.op x x) (M.op x (M.op x x))) := by
          first
          | (have i₁ := b2e12 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : x = y := by
          first
          | (have i₁ := b2e25
             have i₂ := b2e12 x x
             grind)
          | exact superpose b2e12 b2e25
          | exact resolve b2e25 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e30 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e28
             grind)
          | exact superpose b2e28 b2e21
          | exact resolve b2e21 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e31 : False := by grind
        exact b2e31
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e41 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b3e12 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e12 (σ x) (σ x)
             grind)
          | exact superpose b3e12 b3e41
          | exact resolve b3e41 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e46 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e13
          | exact resolve b3e13 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e47 : x = y := by
          first
          | (have i₁ := b3e46
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e46
          | exact resolve b3e46 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e63 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e20
          | exact resolve b3e20 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e64 : False := by grind
        exact b3e64
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
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
          have b4e33 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X1 X1) (M.op X1 (M.op X0 X1))
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
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
          have b4e43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b4e68 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b4e68
          have b4e72 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e70
            | exact resolve b4e70 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e74 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e69 y
               grind)
            | exact superpose b4e69 b4e72
            | exact resolve b4e72 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e75 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e74
            | exact resolve b4e74 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e69 (σ X0)
               grind)
            | exact superpose b4e69 b4e19
            | exact resolve b4e19 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e69 (τ X0)
               grind)
            | exact superpose b4e69 b4e26
            | exact resolve b4e26 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e80 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e80
            | exact resolve b4e80 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e77 X0
               have i₂ := b4e69 X0
               grind)
            | exact superpose b4e69 b4e77
            | exact resolve b4e77 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e89 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e83 X0
               have i₂ := b4e69 X0
               grind)
            | exact superpose b4e69 b4e83
            | exact resolve b4e83 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e115 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1))) = X2 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X1
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X0
               have i₂ := b4e18 X0 X0
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e193 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e89 X0
               grind)
            | exact superpose b4e89 b4e14
            | exact resolve b4e14 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e248 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (τ X0) X1
               have i₂ := b4e193 X0
               grind)
            | exact superpose b4e193 b4e16
            | (have j0 := b4e16 (τ X0) X1
               grind)
            | exact resolve b4e16 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1202 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 X1)
               have i₂ := b4e115 X0 X1 X0
               grind)
            | exact superpose b4e115 b4e13
            | (have j1 := b4e115 X0 X1 x
               grind)
            | exact resolve b4e13 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e6692 : ∀ X0 X1 : G, (M.op X1 (τ (τ X0))) ≠ (τ (τ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (τ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e248 (τ X0) X1
               have i₂ := b4e193 X0
               grind)
            | exact superpose b4e193 b4e248
            | (have j0 := b4e248 (τ X0) X1
               grind)
            | (have r₁ := b4e248 X0 (τ X0)
               have r₂ := b4e193 X0
               grind)
            | exact resolve b4e248 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e18392 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (M.op (M.op X0 X1) (M.op X0 X1)) X0
               have i₂ := b4e1202 X0 X1
               grind)
            | exact superpose b4e1202 b4e33
            | (have j1 := b4e1202 X1 X0
               grind)
            | exact resolve b4e33 b4e1202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e1202
          have b4e18465 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e18392 X0 X1
               have i₂ := b4e13 (M.op X1 X0) (M.op X1 X0)
               grind)
            | exact superpose b4e13 b4e18392
            | (have j0 := b4e18392 X0 X1
               grind)
            | exact resolve b4e18392 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18392
          have b4e18466 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18465 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18465
          have b4e18801 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18466 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18466 X0 X1
               grind)
            | exact superpose b4e18466 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e18466 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18466 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18466 X0 X0
               grind)
            | exact resolve b4e17 b4e18466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e18896 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e18466 (τ X1) X0
               grind)
            | exact superpose b4e18466 b4e25
            | (have j1 := b4e18466 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e18466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e18906 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 X0 X1
               have i₂ := b4e18466 (τ X1) (τ X0)
               grind)
            | exact superpose b4e18466 b4e43
            | (have j1 := b4e18466 (τ X1) (τ X0)
               grind)
            | exact resolve b4e43 b4e18466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e18928 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18801 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18801
          have b4e18942 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e18906 X0 X1
               have i₂ := b4e193 X0
               grind)
            | exact superpose b4e193 b4e18906
            | (have j0 := b4e18906 X0 X1
               grind)
            | exact resolve b4e18906 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18906
          have b4e28081 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e18896 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e18896
            | exact resolve b4e18896 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18896
          have b4e28404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e28081 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e28081
            | (have j0 := b4e28081 X0 X1
               grind)
            | exact resolve b4e28081 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28081
          have b4e29817 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e28404 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e28404 X0 X1
               grind)
            | exact superpose b4e28404 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e28404 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e28404 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e28404 X0 X0
               grind)
            | exact resolve b4e17 b4e28404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29899 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e29817 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29817
          have b4e92735 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e248 X0 (τ X1)
               have i₂ := b4e18942 X1 X0
               grind)
            | exact superpose b4e18942 b4e248
            | (have j0 := b4e248 X0 (τ X1)
               have j1 := b4e18942 X1 X0
               grind)
            | (have r₁ := b4e248 X1 (τ X1)
               have r₂ := b4e18942 X1 X1
               grind)
            | exact resolve b4e248 b4e18942
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e248
          have b4e93035 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e18942 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93036 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e18942 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18942
          have b4e93062 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e92735 X0 X1
               have i₂ := b4e193 X1
               grind)
            | exact superpose b4e193 b4e92735
            | (have j0 := b4e92735 X0 X1
               grind)
            | exact resolve b4e92735 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193 b4e92735
          have b4e93221 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e93062 X0 X1
               have i₂ := b4e43 X1 X0
               grind)
            | exact superpose b4e43 b4e93062
            | (have j0 := b4e93062 X0 X1
               grind)
            | exact resolve b4e93062 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e93062
          have b4e93323 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e93221 X0 X1
               have j1 := b4e93036 X1 X0
               grind)
            | (have r₁ := b4e93221 X1 X0
               have r₂ := b4e93036 X0 X1
               grind)
            | exact resolve b4e93221 b4e93036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93036 b4e93221
          have b4e93736 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X1) (σ X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93035 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e93035
            | exact resolve b4e93035 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93035
          have b4e93906 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X1 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93736 X0 X1
               have i₂ := b4e86 X1
               grind)
            | exact superpose b4e86 b4e93736
            | (have j0 := b4e93736 X0 X1
               grind)
            | exact resolve b4e93736 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93736
          have b4e93937 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93906 X0 X1
               have i₂ := b4e14 (M.op X1 X1)
               grind)
            | exact superpose b4e14 b4e93906
            | (have j0 := b4e93906 X0 X1
               grind)
            | exact resolve b4e93906 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93906
          have b4e93959 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93937 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e93937
            | (have j0 := b4e93937 X0 X1
               grind)
            | exact resolve b4e93937 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93937
          have b4e93975 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e93959 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e93959
            | (have j0 := b4e93959 X0 X1
               grind)
            | exact resolve b4e93959 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93959
          have b4e93989 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e93975 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e93975
            | (have j0 := b4e93975 X0 X1
               grind)
            | exact resolve b4e93975 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93975
          have b4e93995 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e93989 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e93989
            | (have j0 := b4e93989 X0 X1
               grind)
            | exact resolve b4e93989 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93989
          have b4e115033 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93323 (σ X0) (σ X1)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e93323
            | (have j0 := b4e93323 (σ X0) (σ X1)
               grind)
            | exact resolve b4e93323 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e115061 : ∀ X0 X1 : G, (k (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e93323 X0 (σ X1)
               have i₂ := b4e30 X0 X1
               grind)
            | exact superpose b4e30 b4e93323
            | (have j0 := b4e93323 X0 (σ X1)
               grind)
            | exact resolve b4e93323 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e93323
          have b4e115210 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (τ (M.op (σ X1) (σ X1))) ∨ (k (τ X0) X1) ≠ (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e115061 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e115061
            | (have j0 := b4e115061 X0 X1
               grind)
            | exact resolve b4e115061 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115061
          have b4e115231 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X0 X0))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e115033 X0 X1
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e115033
            | (have j0 := b4e115033 X0 X1
               grind)
            | exact resolve b4e115033 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115033
          have b4e115262 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (τ (σ (M.op X1 X1))) ∨ (k (τ X0) X1) ≠ (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e115210 X0 X1
               have i₂ := b4e86 X1
               grind)
            | exact superpose b4e86 b4e115210
            | (have j0 := b4e115210 X0 X1
               grind)
            | exact resolve b4e115210 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115210
          have b4e115279 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e115231 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e115231
            | (have j0 := b4e115231 X0 X1
               grind)
            | exact resolve b4e115231 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115231
          have b4e115296 : ∀ X0 X1 : G, (k (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e115262 X0 X1
               have i₂ := b4e14 (M.op X1 X1)
               grind)
            | exact superpose b4e14 b4e115262
            | (have j0 := b4e115262 X0 X1
               grind)
            | exact resolve b4e115262 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115262
          have b4e115304 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e115279 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e115279
            | (have j0 := b4e115279 X0 X1
               grind)
            | exact resolve b4e115279 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115279
          have b4e115323 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e115304 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e115304
            | (have j0 := b4e115304 X0 X1
               grind)
            | exact resolve b4e115304 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115304
          have b4e115336 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e115323 X0 X1
               have i₂ := b4e86 X1
               grind)
            | exact superpose b4e86 b4e115323
            | (have j0 := b4e115323 X0 X1
               grind)
            | exact resolve b4e115323 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115323
          have b4e115343 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X1 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e115336 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e115336
            | (have j0 := b4e115336 X0 X1
               grind)
            | exact resolve b4e115336 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115336
          have b4e115345 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e115343 X0 X1
               have i₂ := b4e14 (M.op X1 X1)
               grind)
            | exact superpose b4e14 b4e115343
            | (have j0 := b4e115343 X0 X1
               grind)
            | exact resolve b4e115343 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115343
          have b4e116844 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (k (σ y) X0) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e115345 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e115345
            | (have j0 := b4e115345 (σ y) X0
               grind)
            | exact resolve b4e115345 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115345
          have b4e116982 : ∀ X0 : G, (k (σ y) X0) ≠ (σ (M.op y x)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e116844 X0
               have i₂ := b4e75
               grind)
            | exact superpose b4e75 b4e116844
            | (have j0 := b4e116844 X0
               grind)
            | exact resolve b4e116844 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116844
          have b4e120104 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) ≠ (k (τ (σ y)) X0) ∨ (M.op X0 X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e115296 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e115296
            | (have j0 := b4e115296 (σ y) X0
               grind)
            | exact resolve b4e115296 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115296
          have b4e120155 : ∀ X0 : G, (k y X0) ≠ (τ (M.op (σ y) (σ x))) ∨ (M.op X0 X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e120104 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e120104
            | (have j0 := b4e120104 X0
               grind)
            | exact resolve b4e120104 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120104
          have b4e120184 : ∀ X0 : G, (k y X0) ≠ (τ (σ (M.op y x))) ∨ (M.op X0 X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e120155 X0
               have i₂ := b4e75
               grind)
            | exact superpose b4e75 b4e120155
            | (have j0 := b4e120155 X0
               grind)
            | exact resolve b4e120155 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e120155
          have b4e120196 : ∀ X0 : G, (M.op y x) ≠ (k y X0) ∨ (M.op X0 X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e120184 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e120184
            | (have j0 := b4e120184 X0
               grind)
            | exact resolve b4e120184 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120184
          have b4e120205 : ∀ X0 : G, (M.op y x) ≠ (k y X0) ∨ (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e120196 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e120196
            | (have j0 := b4e120196 X0
               grind)
            | exact resolve b4e120196 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120196
          have b4e131381 : ∀ X0 : G, (σ (M.op y x)) ≠ (σ (k y X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e116982 (σ X0)
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e116982
            | (have j0 := b4e116982 (σ X0)
               grind)
            | exact resolve b4e116982 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116982
          have b4e131461 : ∀ X0 : G, (σ (M.op y x)) ≠ (σ (k y X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e131381 X0
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e131381
            | (have j0 := b4e131381 X0
               grind)
            | exact resolve b4e131381 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131381
          have b4e165677 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (k (τ (τ X1)) X0) ∨ (M.op X0 (τ (τ X1))) = (k (τ (τ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e6692 X1 X0
               have i₂ := b4e18466 (τ (τ X1)) X0
               grind)
            | (have i₁ := b4e6692 X0 (τ (τ X0))
               have i₂ := b4e18466 X0 (τ (τ X0))
               grind)
            | exact superpose b4e18466 b4e6692
            | (have j0 := b4e6692 X1 X0
               have j1 := b4e18466 (τ (τ X1)) X0
               grind)
            | exact resolve b4e6692 b4e18466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6692 b4e18466
          have b4e165715 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (τ (M.op X1 X1))) ∨ (M.op X0 (τ (τ X1))) = (k (τ (τ X1)) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e165677 X0 X1
               have j1 := b4e93995 (τ (τ X1)) X0
               grind)
            | (have r₁ := b4e165677 X1 X1
               have r₂ := b4e93995 (τ (τ X1)) X1
               grind)
            | (have r₁ := b4e165677 (τ (τ X1)) X1
               have r₂ := b4e93995 (τ (τ X1)) (τ (τ X1))
               grind)
            | exact resolve b4e165677 b4e93995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93995 b4e165677
          have b4e287593 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (τ (σ (M.op X0 X0)))) ∨ (M.op X1 (τ (τ (σ X0)))) = (k (τ (τ (σ X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e165715 X1 (σ X0)
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e165715
            | (have j0 := b4e165715 X1 (σ X0)
               grind)
            | exact resolve b4e165715 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165715
          have b4e287605 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 (τ (τ (σ X0)))) = (k (τ (τ (σ X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e287593 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e287593
            | (have j0 := b4e287593 X0 X1
               grind)
            | exact resolve b4e287593 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287593
          have b4e287608 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e287605 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e287605
            | (have j0 := b4e287605 X0 X1
               grind)
            | exact resolve b4e287605 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287605
          have b4e292946 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e287608 (σ X0) X1
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e287608
            | (have j0 := b4e287608 (σ X0) X1
               grind)
            | exact resolve b4e287608 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287608
          have b4e292987 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e292946 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e292946
            | (have j0 := b4e292946 X0 X1
               grind)
            | (have r₁ := b4e292946 X1 X1
               have r₂ := b4e14 (M.op X1 X1)
               grind)
            | exact resolve b4e292946 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292946
          have b4e293005 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e292987 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e292987
            | (have j0 := b4e292987 X0 X1
               grind)
            | exact resolve b4e292987 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292987
          have b4e786782 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18928 X0 X1
               grind)
            | exact superpose b4e18928 b4e16
            | (have j1 := b4e18928 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18928 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18928 X1 X1
               grind)
            | exact resolve b4e16 b4e18928
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e18928
          have b4e786809 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e786782 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e786782
          have b4e786826 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e786809 X0 X1
               have j1 := b4e293005 X0 X1
               grind)
            | (have r₁ := b4e786809 X0 X1
               have r₂ := b4e293005 X0 X1
               grind)
            | (have r₁ := b4e786809 X1 X0
               have r₂ := b4e293005 X0 X1
               grind)
            | exact resolve b4e786809 b4e293005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293005 b4e786809
          have b4e786870 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e786826 X0 X1
               have i₂ := b4e69 X0
               grind)
            | exact superpose b4e69 b4e786826
            | (have j0 := b4e786826 X0 X1
               grind)
            | exact resolve b4e786826 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69 b4e786826
          have b4e805162 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X0 X1
               have i₂ := b4e786870 (σ X0) X1
               grind)
            | exact superpose b4e786870 b4e40
            | (have j1 := b4e786870 (σ X0) X1
               grind)
            | exact resolve b4e40 b4e786870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e805284 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e786870 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e786870
          have b4e805331 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e805162 X0 X1
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e805162
            | (have j0 := b4e805162 X0 X1
               grind)
            | exact resolve b4e805162 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86 b4e805162
          have b4e805367 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e805331 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e805331
            | (have j0 := b4e805331 X0 X1
               grind)
            | exact resolve b4e805331 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e805331
          have b4e813475 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e805284 X1 X0
               have i₂ := b4e28404 X1 X0
               grind)
            | (have i₁ := b4e805284 X1 X1
               have i₂ := b4e28404 X0 X1
               grind)
            | exact superpose b4e28404 b4e805284
            | (have j0 := b4e805284 X1 X0
               have j1 := b4e28404 X1 X0
               grind)
            | (have r₁ := b4e805284 X0 X0
               have r₂ := b4e28404 X0 X0
               grind)
            | exact resolve b4e805284 b4e28404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28404 b4e805284
          have b4e813552 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e813475 X0 X1
               have j1 := b4e29899 X0 X1
               grind)
            | (have r₁ := b4e813475 X0 X1
               have r₂ := b4e29899 X0 X1
               grind)
            | (have r₁ := b4e813475 X1 X0
               have r₂ := b4e29899 X0 X1
               grind)
            | exact resolve b4e813475 b4e29899
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29899 b4e813475
          have b4e836622 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e805367 X1 (σ X0)
               grind)
            | exact superpose b4e805367 b4e19
            | (have j1 := b4e805367 X1 (σ X0)
               grind)
            | exact resolve b4e19 b4e805367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e805367
          have b4e836652 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e836622 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e836622
            | (have j0 := b4e836622 X0 X1
               grind)
            | exact resolve b4e836622 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e836622
          have b4e855450 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e836652 x y
               grind)
            | exact superpose b4e836652 b4e20
            | (have j1 := b4e836652 x y
               grind)
            | exact resolve b4e20 b4e836652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e836652
          have b4e855504 : (M.op y y) = (k y x) := by
            first
            | (have j1 := b4e813552 x y
               grind)
            | (have r₁ := b4e855450
               have r₂ := b4e813552 x y
               grind)
            | exact resolve b4e855450 b4e813552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e813552 b4e855450
          have b4e855537 : (M.op y x) = (k y x) := by
            first
            | (have i₁ := b4e855504
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e855504
            | exact resolve b4e855504 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e855504
          have b4e867653 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e120205 x
               have i₂ := b4e855537
               grind)
            | exact superpose b4e855537 b4e120205
            | (have j0 := b4e120205 x
               grind)
            | (have r₁ := b4e120205 x
               have r₂ := b4e855537
               grind)
            | exact resolve b4e120205 b4e855537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120205
          have b4e867654 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e131461 x
               have i₂ := b4e855537
               grind)
            | exact superpose b4e855537 b4e131461
            | (have j0 := b4e131461 x
               grind)
            | exact resolve b4e131461 b4e855537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131461 b4e855537
          have b4e867717 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b4e867654
          have b4e867718 : (M.op x y) = (M.op x x) := by grind
          clear b4e867653
          have b4e892108 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e867717
               grind)
            | exact superpose b4e867717 b4e20
            | exact resolve b4e20 b4e867717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e867717
          have b4e892176 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e892108
               have i₂ := b4e867718
               grind)
            | exact superpose b4e867718 b4e892108
            | exact resolve b4e892108 b4e867718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e867718 b4e892108
          have b4e892177 : False := by grind
          exact b4e892177
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b5e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e65 (σ X0)
               grind)
            | exact superpose b5e65 b5e19
            | exact resolve b5e19 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e69 X0
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e69
            | exact resolve b5e69 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e69
          have b5e86 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e122 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e311 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e86 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e312 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e311
               have r₂ := b5e21
               grind)
            | exact resolve b5e311 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e311
          have b5e1670 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e122 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122
          have b5e1671 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1670
               have r₂ := b5e23
               grind)
            | exact resolve b5e1670 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1670
          have b5e1672 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1671
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1671
            | exact resolve b5e1671 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1671
          have b5e1673 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1672
               have i₂ := b5e312
               grind)
            | exact superpose b5e312 b5e1672
            | exact resolve b5e1672 b5e312
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e312 b5e1672
          have b5e1677 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1673
               grind)
            | exact superpose b5e1673 b5e23
            | exact resolve b5e23 b5e1673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1673
          have b5e1694 : False := by grind
          exact b5e1694
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b6e12 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e12 (σ x) (σ x)
             grind)
          | exact superpose b6e12 b6e39
          | exact resolve b6e39 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e44 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e13
          | exact resolve b6e13 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e45 : x = y := by
          first
          | (have i₁ := b6e44
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e44
          | exact resolve b6e44 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e56 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e45
             grind)
          | exact superpose b6e45 b6e20
          | exact resolve b6e20 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e57 : False := by grind
        exact b6e57
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b7e64
          have b7e67 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e68 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e65 y
               grind)
            | exact superpose b7e65 b7e67
            | exact resolve b7e67 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b7e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e70 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e70
            | exact resolve b7e70 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e70
          have b7e87 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
            | (have i₁ := b7e87 X0
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e87
            | (have j0 := b7e87 X0
               grind)
            | exact resolve b7e87 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e91 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e23
            | exact resolve b7e23 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e91
            | exact resolve b7e91 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e131 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e111 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e955 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e90 (σ x)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e90
            | (have j0 := b7e90 (σ x)
               grind)
            | (have r₁ := b7e90 (σ x)
               have r₂ := b7e68
               grind)
            | exact resolve b7e90 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e90
          have b7e958 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e955
          have b7e959 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e958
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e958
            | exact resolve b7e958 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e958
          have b7e960 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e959
               have r₂ := b7e96
               grind)
            | exact resolve b7e959 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e959
          have b7e961 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e960
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e960
            | exact resolve b7e960 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e960
          have b7e962 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e961
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e961
            | exact resolve b7e961 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e961
          have b7e964 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e962
               have i₂ := b7e131 x y
               grind)
            | exact superpose b7e131 b7e962
            | (have j1 := b7e131 x y
               grind)
            | exact resolve b7e962 b7e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131
          have b7e967 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e962
               grind)
            | exact superpose b7e962 b7e14
            | exact resolve b7e14 b7e962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e962
          have b7e988 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e967
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e967
            | exact resolve b7e967 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e967
          have b7e991 : (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e964
               have r₂ := b7e96
               grind)
            | exact resolve b7e964 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96 b7e964
          have b7e994 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e991
               have r₂ := b7e22
               grind)
            | exact resolve b7e991 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e991
          have b7e995 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e994
               have i₂ := b7e988
               grind)
            | exact superpose b7e988 b7e994
            | exact resolve b7e994 b7e988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e988 b7e994
          have b7e996 : False := by grind
          exact b7e996
        · have b8e13 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X0 X1))) = X0 := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e31 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (M.op X1 X1) (M.op X1 (M.op X0 X1))
               have i₂ := b8e13 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
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
          clear b8e30
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
          have b8e66 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e61 (τ X0)
               grind)
            | exact superpose b8e61 b8e26
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e69 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e66 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e66
            | exact resolve b8e66 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
          clear b8e63
          have b8e75 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e69 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e69
            | exact resolve b8e69 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e102 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1))) = X2 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 X1
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e13 X0 X0
               have i₂ := b8e18 X0 X0
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e151 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e14
            | exact resolve b8e14 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e238 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (τ X0) X1
               have i₂ := b8e151 X0
               grind)
            | exact superpose b8e151 b8e16
            | (have j0 := b8e16 (τ X0) X1
               grind)
            | exact resolve b8e16 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e728 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X1)
               have i₂ := b8e102 X0 X1 X0
               grind)
            | exact superpose b8e102 b8e13
            | (have j1 := b8e102 X0 X1 x
               grind)
            | exact resolve b8e13 b8e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e6263 : ∀ X0 X1 : G, (M.op X1 (τ (τ X0))) ≠ (τ (τ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (τ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e238 (τ X0) X1
               have i₂ := b8e151 X0
               grind)
            | exact superpose b8e151 b8e238
            | (have j0 := b8e238 (τ X0) X1
               grind)
            | (have r₁ := b8e238 X0 (τ X0)
               have r₂ := b8e151 X0
               grind)
            | exact resolve b8e238 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10831 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e31 (M.op (M.op X0 X1) (M.op X0 X1)) X0
               have i₂ := b8e728 X0 X1
               grind)
            | exact superpose b8e728 b8e31
            | (have j1 := b8e728 X1 X0
               grind)
            | exact resolve b8e31 b8e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e728
          have b8e10884 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10831 X0 X1
               have i₂ := b8e13 (M.op X1 X0) (M.op X1 X0)
               grind)
            | exact superpose b8e13 b8e10831
            | (have j0 := b8e10831 X0 X1
               grind)
            | exact resolve b8e10831 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10831
          have b8e10885 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e10884 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10884
          have b8e11105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e10885 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e10885 X0 X1
               grind)
            | exact superpose b8e10885 b8e17
            | (have j0 := b8e17 X0 X0
               have j1 := b8e10885 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e10885 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e10885 X0 X0
               grind)
            | exact resolve b8e17 b8e10885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11180 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e10885 (τ X1) X0
               grind)
            | exact superpose b8e10885 b8e25
            | (have j1 := b8e10885 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e10885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e11181 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e41 X0 X1
               have i₂ := b8e10885 (τ X1) (τ X0)
               grind)
            | exact superpose b8e10885 b8e41
            | (have j1 := b8e10885 (τ X1) (τ X0)
               grind)
            | exact resolve b8e41 b8e10885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11191 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e11105 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11105
          have b8e11201 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e11181 X0 X1
               have i₂ := b8e151 X0
               grind)
            | exact superpose b8e151 b8e11181
            | (have j0 := b8e11181 X0 X1
               grind)
            | exact resolve b8e11181 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11181
          have b8e20233 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e11180 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e11180
            | exact resolve b8e11180 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11180
          have b8e20543 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e20233 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e20233
            | (have j0 := b8e20233 X0 X1
               grind)
            | exact resolve b8e20233 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20233
          have b8e20885 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e20543 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e20543 X0 X1
               grind)
            | exact superpose b8e20543 b8e17
            | (have j0 := b8e17 X0 X0
               have j1 := b8e20543 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e20543 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e20543 X0 X0
               grind)
            | exact resolve b8e17 b8e20543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e20954 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e20885 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20885
          have b8e71178 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e238 X0 (τ X1)
               have i₂ := b8e11201 X1 X0
               grind)
            | exact superpose b8e11201 b8e238
            | (have j0 := b8e238 X0 (τ X1)
               have j1 := b8e11201 X1 X0
               grind)
            | (have r₁ := b8e238 X1 (τ X1)
               have r₂ := b8e11201 X1 X1
               grind)
            | exact resolve b8e238 b8e11201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238
          have b8e71455 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e11201 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e71456 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e11201 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11201
          have b8e71480 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e71178 X0 X1
               have i₂ := b8e151 X1
               grind)
            | exact superpose b8e151 b8e71178
            | (have j0 := b8e71178 X0 X1
               grind)
            | exact resolve b8e71178 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151 b8e71178
          have b8e71636 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e71480 X0 X1
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e71480
            | (have j0 := b8e71480 X0 X1
               grind)
            | exact resolve b8e71480 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e71480
          have b8e71732 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e71636 X0 X1
               have j1 := b8e71456 X1 X0
               grind)
            | (have r₁ := b8e71636 X1 X0
               have r₂ := b8e71456 X0 X1
               grind)
            | exact resolve b8e71636 b8e71456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71456 b8e71636
          have b8e72572 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X1) (σ X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e71455 (σ X1) (σ X0)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e71455
            | exact resolve b8e71455 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71455
          have b8e72722 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X1 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e72572 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e72572
            | (have j0 := b8e72572 X0 X1
               grind)
            | exact resolve b8e72572 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72572
          have b8e72739 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e72722 X0 X1
               have i₂ := b8e14 (M.op X1 X1)
               grind)
            | exact superpose b8e14 b8e72722
            | (have j0 := b8e72722 X0 X1
               grind)
            | exact resolve b8e72722 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72722
          have b8e72751 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e72739 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e72739
            | (have j0 := b8e72739 X0 X1
               grind)
            | exact resolve b8e72739 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72739
          have b8e72759 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e72751 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e72751
            | (have j0 := b8e72751 X0 X1
               grind)
            | exact resolve b8e72751 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72751
          have b8e72765 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e72759 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e72759
            | (have j0 := b8e72759 X0 X1
               grind)
            | exact resolve b8e72759 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72759
          have b8e72768 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e72765 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e72765
            | (have j0 := b8e72765 X0 X1
               grind)
            | exact resolve b8e72765 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72765
          have b8e79448 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e71732 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e71732
            | (have j0 := b8e71732 (σ X0) (σ X1)
               grind)
            | exact resolve b8e71732 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71732
          have b8e79605 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X0 X0))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79448 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e79448
            | (have j0 := b8e79448 X0 X1
               grind)
            | exact resolve b8e79448 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79448
          have b8e79638 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79605 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e79605
            | (have j0 := b8e79605 X0 X1
               grind)
            | exact resolve b8e79605 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79605
          have b8e79650 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79638 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e79638
            | (have j0 := b8e79638 X0 X1
               grind)
            | exact resolve b8e79638 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79638
          have b8e79659 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e79650 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e79650
            | (have j0 := b8e79650 X0 X1
               grind)
            | exact resolve b8e79650 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79650
          have b8e79664 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e79659 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e79659
            | (have j0 := b8e79659 X0 X1
               grind)
            | exact resolve b8e79659 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79659
          have b8e79669 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X1 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e79664 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e79664
            | (have j0 := b8e79664 X0 X1
               grind)
            | exact resolve b8e79664 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79664
          have b8e79670 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e79669 X0 X1
               have i₂ := b8e14 (M.op X1 X1)
               grind)
            | exact superpose b8e14 b8e79669
            | (have j0 := b8e79669 X0 X1
               grind)
            | exact resolve b8e79669 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79669
          have b8e80020 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e79670 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e79670
            | (have j0 := b8e79670 (σ X0) (σ X1)
               grind)
            | exact resolve b8e79670 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e80077 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e80020 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e80020
            | (have j0 := b8e80020 X0 X1
               grind)
            | exact resolve b8e80020 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80020
          have b8e80095 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e80077 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e80077
            | (have j0 := b8e80077 X0 X1
               grind)
            | exact resolve b8e80077 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80077
          have b8e111413 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (k (τ (τ X1)) X0) ∨ (M.op X0 (τ (τ X1))) = (k (τ (τ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e6263 X1 X0
               have i₂ := b8e10885 (τ (τ X1)) X0
               grind)
            | (have i₁ := b8e6263 X0 (τ (τ X0))
               have i₂ := b8e10885 X0 (τ (τ X0))
               grind)
            | exact superpose b8e10885 b8e6263
            | (have j0 := b8e6263 X1 X0
               have j1 := b8e10885 (τ (τ X1)) X0
               grind)
            | exact resolve b8e6263 b8e10885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6263 b8e10885
          have b8e111590 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (τ (τ (M.op X1 X1))) ∨ (M.op X0 (τ (τ X1))) = (k (τ (τ X1)) X0) := by
            intro X0 X1
            first
            | (have j0 := b8e111413 X0 X1
               have j1 := b8e72768 (τ (τ X1)) X0
               grind)
            | (have r₁ := b8e111413 X1 X1
               have r₂ := b8e72768 (τ (τ X1)) X1
               grind)
            | (have r₁ := b8e111413 (τ (τ X1)) X1
               have r₂ := b8e72768 (τ (τ X1)) (τ (τ X1))
               grind)
            | exact resolve b8e111413 b8e72768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72768 b8e111413
          have b8e195110 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (τ (σ (M.op X0 X0)))) ∨ (M.op X1 (τ (τ (σ X0)))) = (k (τ (τ (σ X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e111590 X1 (σ X0)
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e111590
            | (have j0 := b8e111590 X1 (σ X0)
               grind)
            | exact resolve b8e111590 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111590
          have b8e195117 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 (τ (τ (σ X0)))) = (k (τ (τ (σ X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e195110 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e195110
            | (have j0 := b8e195110 X0 X1
               grind)
            | exact resolve b8e195110 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195110
          have b8e195119 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e195117 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e195117
            | (have j0 := b8e195117 X0 X1
               grind)
            | exact resolve b8e195117 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195117
          have b8e195628 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e195119 (σ X0) X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e195119
            | (have j0 := b8e195119 (σ X0) X1
               grind)
            | exact resolve b8e195119 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195119
          have b8e195653 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e195628 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e195628
            | (have j0 := b8e195628 X0 X1
               grind)
            | (have r₁ := b8e195628 X1 X1
               have r₂ := b8e14 (M.op X1 X1)
               grind)
            | exact resolve b8e195628 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195628
          have b8e195663 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e195653 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e195653
            | (have j0 := b8e195653 X0 X1
               grind)
            | exact resolve b8e195653 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195653
          have b8e326910 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e11191 X0 X1
               grind)
            | exact superpose b8e11191 b8e16
            | (have j1 := b8e11191 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e11191 X0 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e11191 X1 X1
               grind)
            | exact resolve b8e16 b8e11191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e326921 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 X1
               have i₂ := b8e11191 X1 (σ X0)
               grind)
            | exact superpose b8e11191 b8e38
            | (have j1 := b8e11191 (σ X0) X1
               grind)
            | exact resolve b8e38 b8e11191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e11191
          have b8e326937 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e326910 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326910
          have b8e326946 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e326921 X0 X1
               have j1 := b8e195663 (σ X0) X1
               grind)
            | (have r₁ := b8e326921 X0 X1
               have r₂ := b8e195663 (σ X0) X1
               grind)
            | (have r₁ := b8e326921 X0 X0
               have r₂ := b8e195663 X0 (σ X0)
               grind)
            | exact resolve b8e326921 b8e195663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326921
          have b8e326953 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e326937 X0 X1
               have j1 := b8e195663 X0 X1
               grind)
            | (have r₁ := b8e326937 X0 X1
               have r₂ := b8e195663 X0 X1
               grind)
            | (have r₁ := b8e326937 X1 X0
               have r₂ := b8e195663 X0 X1
               grind)
            | exact resolve b8e326937 b8e195663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195663 b8e326937
          have b8e326991 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e326946 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e326946
            | (have j0 := b8e326946 X0 X1
               grind)
            | exact resolve b8e326946 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e326946
          have b8e326994 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e326953 X0 X1
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e326953
            | (have j0 := b8e326953 X0 X1
               grind)
            | exact resolve b8e326953 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e326953
          have b8e326999 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e326991 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e326991
            | (have j0 := b8e326991 X0 X1
               grind)
            | exact resolve b8e326991 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326991
          have b8e331281 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e326994 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326994
          have b8e331677 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e331281 X1 X0
               have i₂ := b8e20543 X1 X0
               grind)
            | (have i₁ := b8e331281 X1 X1
               have i₂ := b8e20543 X0 X1
               grind)
            | exact superpose b8e20543 b8e331281
            | (have j0 := b8e331281 X1 X0
               have j1 := b8e20543 X1 X0
               grind)
            | (have r₁ := b8e331281 X0 X0
               have r₂ := b8e20543 X0 X0
               grind)
            | exact resolve b8e331281 b8e20543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20543 b8e331281
          have b8e331750 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e331677 X0 X1
               have j1 := b8e20954 X0 X1
               grind)
            | (have r₁ := b8e331677 X0 X1
               have r₂ := b8e20954 X0 X1
               grind)
            | (have r₁ := b8e331677 X1 X0
               have r₂ := b8e20954 X0 X1
               grind)
            | exact resolve b8e331677 b8e20954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20954 b8e331677
          have b8e342116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e326999 X1 (σ X0)
               grind)
            | exact superpose b8e326999 b8e19
            | (have j1 := b8e326999 X1 (σ X0)
               grind)
            | exact resolve b8e19 b8e326999
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326999
          have b8e342151 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e342116 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e342116
            | (have j0 := b8e342116 X0 X1
               grind)
            | exact resolve b8e342116 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342116
          have b8e363563 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e342151 x y
               grind)
            | exact superpose b8e342151 b8e20
            | (have j1 := b8e342151 x y
               grind)
            | exact resolve b8e20 b8e342151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342151
          have b8e363676 : (M.op y y) = (k y x) := by
            first
            | (have j1 := b8e331750 x y
               grind)
            | (have r₁ := b8e363563
               have r₂ := b8e331750 x y
               grind)
            | exact resolve b8e363563 b8e331750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e331750 b8e363563
          have b8e368581 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e79670 y x
               have i₂ := b8e363676
               grind)
            | exact superpose b8e363676 b8e79670
            | (have j0 := b8e79670 y x
               grind)
            | (have r₁ := b8e79670 y x
               have r₂ := b8e363676
               grind)
            | exact resolve b8e79670 b8e363676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79670
          have b8e368582 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e80095 y x
               have i₂ := b8e363676
               grind)
            | exact superpose b8e363676 b8e80095
            | (have j0 := b8e80095 y x
               grind)
            | exact resolve b8e80095 b8e363676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80095 b8e363676
          have b8e368590 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e368582
          have b8e368591 : (M.op x y) = (M.op x x) := by grind
          clear b8e368581
          have b8e375891 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e368590
               grind)
            | exact superpose b8e368590 b8e20
            | exact resolve b8e20 b8e368590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e368590
          have b8e375961 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e375891
               have i₂ := b8e368591
               grind)
            | exact superpose b8e368591 b8e375891
            | exact resolve b8e375891 b8e368591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e368591 b8e375891
          have b8e375962 : False := by grind
          exact b8e375962
