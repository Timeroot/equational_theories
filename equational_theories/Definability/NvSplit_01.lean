import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
      have b0e59 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e62 : False := by grind
      exact b0e62
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
          have b5e47 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e52 : x = y ∨ y = (k x y) := by grind
          clear b5e47
          have b5e53 : y = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e232 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e3021 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e232 x y
               have i₂ := b5e53
               grind)
            | exact superpose b5e53 b5e232
            | (have j0 := b5e232 x y
               grind)
            | exact resolve b5e232 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e232
          have b5e3028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e3021
          have b5e3040 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e3028
               have r₂ := b5e24
               grind)
            | exact resolve b5e3028 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3028
          have b5e3044 : False := by grind
          exact b5e3044
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
          have b7e44 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (σ y) = (σ (k x y)) := by
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
          have b7e59 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
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
          have b7e60 : y = (M.op x y) ∨ x = y := by
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e156 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e171 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e156
               have r₂ := b8e24
               grind)
            | exact resolve b8e156 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e175 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e171
               have r₂ := b8e23
               grind)
            | exact resolve b8e171 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171
          have b8e176 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e175
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e175
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e175
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e175
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e175 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175
          have b8e177 : y = (M.op x y) ∨ x = y := by grind
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

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxy_pyx_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e61 (σ X0)
           grind)
        | exact superpose b0e61 b0e17
        | exact resolve b0e17 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e76 X0
           have i₂ := b0e61 X0
           grind)
        | exact superpose b0e61 b0e76
        | exact resolve b0e76 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61 b0e76
      have b0e475 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e77 x
           grind)
        | exact superpose b0e77 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e77 x
           grind)
        | exact resolve b0e22 b0e77
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e77
      have b0e488 : False := by grind
      exact b0e488
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
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
        have b1e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e27 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
          intro X0 X1 X2 X3 X5
          first
          | (have i₁ := b1e12 (M.op X0 X2) X3 (M.op x X1) X5
             have i₂ := b1e12 X0 X1 X2 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) (M.op x x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 y X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b1e12 X0 X1 x X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e29 x X1 X2 X3 x
             have i₂ := b1e12 X2 X1 x x
             grind)
          | exact superpose b1e12 b1e29
          | exact resolve b1e29 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e31 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e28 X0 x
             have i₂ := b1e12 X0 x x x
             grind)
          | exact superpose b1e12 b1e28
          | exact resolve b1e28 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e32 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e27 X0 x X2 X3 x
             have i₂ := b1e12 X0 X3 x x
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e51 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ y) X0 (σ x) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e51 X0 x
             have i₂ := b1e12 (σ x) X0 (σ x) x
             grind)
          | exact superpose b1e12 b1e51
          | exact resolve b1e51 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e76 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 x) ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e31 X0
             grind)
          | exact superpose b1e31 b1e15
          | (have j0 := b1e15 X0 x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e31 x
             grind)
          | (have r₁ := b1e15 y x
             have r₂ := b1e31 y
             grind)
          | exact resolve b1e15 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e80 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y x) := by
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
        have b1e83 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 (M.op X0 X1) X2
             have i₂ := b1e12 X0 X1 X1 X0
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 (M.op X0 X1) X2
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e86 : (k x y) = (M.op y x) := by grind
        clear b1e80
        have b1e88 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e83 X0 X1 X2
             have i₂ := b1e32 X0 X1 X2
             grind)
          | exact superpose b1e32 b1e83
          | (have j0 := b1e83 X0 X1 X2
             grind)
          | (have r₁ := b1e83 X0 X2 X2
             have r₂ := b1e32 X0 X2 X2
             grind)
          | exact resolve b1e83 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83
        have b1e95 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 X1) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e88 X0 X1 X2
             have i₂ := b1e30 X1 X2 X0
             grind)
          | exact superpose b1e30 b1e88
          | (have j0 := b1e88 X0 X1 X2
             grind)
          | (have r₁ := b1e88 X2 (M.op x X1) X1
             have r₂ := b1e30 X1 X2 x
             grind)
          | (have r₁ := b1e88 X2 X1 (M.op x X1)
             have r₂ := b1e30 X1 X2 x
             grind)
          | exact resolve b1e88 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e102 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e85 (σ X0)
             grind)
          | exact superpose b1e85 b1e18
          | exact resolve b1e18 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e102 X0
             have i₂ := b1e85 X0
             grind)
          | exact superpose b1e85 b1e102
          | exact resolve b1e102 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102
        have b1e107 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 (M.op x X1) X1
             have i₂ := b1e12 x X1 X1 x
             grind)
          | exact superpose b1e12 b1e16
          | (have j0 := b1e16 (M.op X0 X1) X2
             grind)
          | exact resolve b1e16 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e112 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 (M.op X0 X2)) = (M.op X1 X1) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X1 (M.op X0 X2)
             have i₂ := b1e32 X0 X2 X1
             grind)
          | exact superpose b1e32 b1e16
          | (have j0 := b1e16 X1 (M.op X0 X2)
             grind)
          | (have r₁ := b1e16 x (M.op x X2)
             have r₂ := b1e32 x X2 x
             grind)
          | (have r₁ := b1e16 (M.op X0 X2) X0
             have r₂ := b1e32 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b1e16 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e113 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e115 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e113
        have b1e116 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e115
             have r₂ := b1e21
             grind)
          | exact resolve b1e115 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e115
        have b1e117 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e112 X0 X1 X2
             have i₂ := b1e30 X2 X1 X0
             grind)
          | exact superpose b1e30 b1e112
          | (have j0 := b1e112 X0 X1 X2
             grind)
          | exact resolve b1e112 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112
        have b1e122 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e107 X0 X1 X2
             have i₂ := b1e30 X1 X2 X0
             grind)
          | exact superpose b1e30 b1e107
          | (have j0 := b1e107 X0 X1 X2
             grind)
          | (have r₁ := b1e107 x X1 x
             have r₂ := b1e30 X1 x x
             grind)
          | exact resolve b1e107 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107
        have b1e125 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e116
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e116
          | exact resolve b1e116 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116
        have b1e126 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e117 X0 X1 X2
             have i₂ := b1e30 X2 X1 X0
             grind)
          | exact superpose b1e30 b1e117
          | (have j0 := b1e117 X0 X1 X2
             grind)
          | exact resolve b1e117 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e117
        have b1e131 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e122 X0 X1 X2
             have i₂ := b1e32 X0 X1 X2
             grind)
          | exact superpose b1e32 b1e122
          | (have j0 := b1e122 X0 X1 X2
             grind)
          | (have r₁ := b1e122 X0 x (M.op X0 X2)
             have r₂ := b1e32 X0 X2 x
             grind)
          | (have r₁ := b1e122 (M.op X0 X2) x X0
             have r₂ := b1e32 X0 X2 x
             grind)
          | exact resolve b1e122 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e133 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e125
             have i₂ := b1e86
             grind)
          | exact superpose b1e86 b1e125
          | exact resolve b1e125 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86 b1e125
        have b1e137 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e131 X0 X1 X2
             have i₂ := b1e32 X0 X1 X2
             grind)
          | exact superpose b1e32 b1e131
          | (have j0 := b1e131 X0 X1 X2
             grind)
          | (have r₁ := b1e131 X0 x (M.op X0 X2)
             have r₂ := b1e32 X0 X2 x
             grind)
          | (have r₁ := b1e131 (M.op X0 X2) x X0
             have r₂ := b1e32 X0 X2 x
             grind)
          | exact resolve b1e131 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e167 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X0
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e15 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e198 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X0 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e200 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) X2) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 X1 X0 X2
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e32 X0 X0 x
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e32
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e32 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e207 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e198 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198
        have b1e208 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e207 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e207
        have b1e211 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e167 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167
        have b1e212 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e211 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e211
        have b1e218 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e200 X0 X1 X2
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e200 X0 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b1e15 (M.op X0 X0) (M.op X0 X0)
             grind)
          | (have r₁ := b1e200 X0 X1 X2
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e200 X1 X1 X2
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e200 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e200
        have b1e219 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e208 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e208 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e208 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e208 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e208
        have b1e257 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e218 X0 X1 X2
             have i₂ := b1e32 X0 X0 X2
             grind)
          | exact superpose b1e32 b1e218
          | (have j0 := b1e218 X0 X1 X2
             grind)
          | exact resolve b1e218 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e218
        have b1e303 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e52 X0
             have i₂ := b1e17 X0 (σ y)
             grind)
          | (have i₁ := b1e52 (σ y)
             have i₂ := b1e17 (σ y) x
             grind)
          | exact superpose b1e17 b1e52
          | (have j1 := b1e17 X0 (σ y)
             grind)
          | exact resolve b1e52 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e332 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e303 X0
             have j1 := b1e15 X0 (σ y)
             grind)
          | (have r₁ := b1e303 (σ x)
             have r₂ := b1e15 (σ x) (σ x)
             grind)
          | (have r₁ := b1e303 (σ y)
             have r₂ := b1e15 (σ y) (σ y)
             grind)
          | (have r₁ := b1e303 X0
             have r₂ := b1e15 X0 (σ y)
             grind)
          | exact resolve b1e303 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e303
        have b1e339 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ y)) ∨ (M.op X0 X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e332 X0
             have i₂ := b1e52 X0
             grind)
          | exact superpose b1e52 b1e332
          | (have j0 := b1e332 X0
             grind)
          | exact resolve b1e332 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e332
        have b1e347 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e24 X0 (τ X0)
             have i₂ := b1e85 (τ X0)
             grind)
          | exact superpose b1e85 b1e24
          | exact resolve b1e24 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e352 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e347 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e347
          | exact resolve b1e347 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e347
        have b1e353 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e352 X0
             have i₂ := b1e85 X0
             grind)
          | exact superpose b1e85 b1e352
          | exact resolve b1e352 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e352
        have b1e361 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e25 X1 X0
             grind)
          | exact superpose b1e25 b1e13
          | exact resolve b1e13 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e367 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e133
             grind)
          | exact superpose b1e133 b1e23
          | exact resolve b1e23 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e133
        have b1e391 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e212 (σ X1) (σ X0)
             grind)
          | exact superpose b1e212 b1e18
          | (have j1 := b1e212 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e432 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e391 X0 X1
             have i₂ := b1e103 X1
             grind)
          | exact superpose b1e103 b1e391
          | (have j0 := b1e391 X0 X1
             grind)
          | exact resolve b1e391 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e391
        have b1e559 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e219 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e219
        have b1e564 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e353 X1
             have i₂ := b1e212 (τ X1) X0
             grind)
          | (have i₁ := b1e353 X0
             have i₂ := b1e212 (τ X0) (τ X0)
             grind)
          | exact superpose b1e212 b1e353
          | (have j1 := b1e212 (τ X1) X0
             grind)
          | exact resolve b1e353 b1e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e212
        have b1e1384 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e137 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e137
        have b1e3828 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e353 X1
             have i₂ := b1e257 X0 (τ X1) (τ X1)
             grind)
          | (have i₁ := b1e353 X0
             have i₂ := b1e257 (τ X0) X1 (τ X0)
             grind)
          | exact superpose b1e257 b1e353
          | (have j1 := b1e257 X0 (τ X1) x
             grind)
          | exact resolve b1e353 b1e257
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e257 b1e353
        have b1e4857 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op X0 X1) = (k X0 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e559 X2 (M.op x X1)
             have i₂ := b1e30 X1 X2 x
             grind)
          | exact superpose b1e30 b1e559
          | exact resolve b1e559 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4865 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e559 (M.op X0 X2) x
             have i₂ := b1e32 X0 X2 x
             grind)
          | exact superpose b1e32 b1e559
          | exact resolve b1e559 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e559
        have b1e4942 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X0 X1) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4865 X0 X1 X2
             have i₂ := b1e30 X2 X1 X0
             grind)
          | exact superpose b1e30 b1e4865
          | (have j0 := b1e4865 X0 X1 X2
             grind)
          | (have r₁ := b1e4865 x x x
             have r₂ := b1e30 x x x
             grind)
          | exact resolve b1e4865 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4865
        have b1e4949 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4857 X0 X1 X2
             have i₂ := b1e32 X2 X1 X0
             grind)
          | exact superpose b1e32 b1e4857
          | (have j0 := b1e4857 X0 X1 X2
             grind)
          | (have r₁ := b1e4857 X2 X2 X2
             have r₂ := b1e32 X2 X2 X2
             grind)
          | exact resolve b1e4857 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4857
        have b1e8065 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e1384 x (M.op x X1)
             have i₂ := b1e30 X1 x x
             grind)
          | exact superpose b1e30 b1e1384
          | (have j0 := b1e1384 X0 X1
             grind)
          | exact resolve b1e1384 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e8140 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b1e8065 X0 X1
             have j1 := b1e4942 X0 X0 X1
             grind)
          | (have r₁ := b1e8065 x x
             have r₂ := b1e4942 x x x
             grind)
          | (have r₁ := b1e8065 X0 x
             have r₂ := b1e4942 X0 X0 x
             grind)
          | exact resolve b1e8065 b1e4942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4942 b1e8065
        have b1e12283 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) ∨ (k (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e339 (σ x)
             have i₂ := b1e432 x x
             grind)
          | exact superpose b1e432 b1e339
          | (have j1 := b1e432 x X0
             grind)
          | exact resolve b1e339 b1e432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e339
        have b1e12386 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e432 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e432
        have b1e12418 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 x)) ∨ (k (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e12283 X0
             have i₂ := b1e103 X0
             grind)
          | exact superpose b1e103 b1e12283
          | (have j0 := b1e12283 X0
             grind)
          | exact resolve b1e12283 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12283
        have b1e12565 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e12418 X0
             have j1 := b1e12386 x X0
             grind)
          | (have r₁ := b1e12418 x
             have r₂ := b1e12386 x x
             grind)
          | exact resolve b1e12418 b1e12386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12386 b1e12418
        have b1e12638 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e12565 X0
             have i₂ := b1e18 X0 y
             grind)
          | exact superpose b1e18 b1e12565
          | (have j0 := b1e12565 X0
             grind)
          | exact resolve b1e12565 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12565
        have b1e18304 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e126 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e18322 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e18304 X0 X1
             have j1 := b1e4949 X0 X1 X0
             grind)
          | (have r₁ := b1e18304 x X1
             have r₂ := b1e4949 x X1 x
             grind)
          | (have r₁ := b1e18304 X1 X1
             have r₂ := b1e4949 X1 X1 X1
             grind)
          | exact resolve b1e18304 b1e4949
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4949 b1e18304
        have b1e18595 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e18322 (σ y) X0
             have i₂ := b1e52 X0
             grind)
          | exact superpose b1e52 b1e18322
          | exact resolve b1e18322 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e18630 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (σ X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e361 X0 (M.op (σ X0) X1)
             have i₂ := b1e18322 (σ X0) X1
             grind)
          | exact superpose b1e18322 b1e361
          | exact resolve b1e361 b1e18322
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18322
        have b1e18936 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k y (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b1e361 y (M.op (σ x) X0)
             have i₂ := b1e18595 X0
             grind)
          | exact superpose b1e18595 b1e361
          | exact resolve b1e361 b1e18595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e361 b1e18595
        have b1e215003 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e564 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e564
          | exact resolve b1e564 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e564
        have b1e216313 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e215003 X0 X1
             have i₂ := b1e103 X0
             grind)
          | exact superpose b1e103 b1e215003
          | (have j0 := b1e215003 X0 X1
             grind)
          | exact resolve b1e215003 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e215003
        have b1e217523 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op X0 x)) ∨ (M.op X0 x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e216313 y X0
             have i₂ := b1e31 X0
             grind)
          | exact superpose b1e31 b1e216313
          | exact resolve b1e216313 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e218438 : ∀ X0 : G, (σ (M.op y x)) = (σ (M.op X0 x)) ∨ (M.op X0 x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e217523 X0
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e217523
          | (have j0 := b1e217523 X0
             grind)
          | exact resolve b1e217523 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e217523
        have b1e222904 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y x)) ∨ (M.op X0 x) = (k x X0) ∨ (M.op X0 x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e216313 x X0
             have i₂ := b1e218438 X0
             grind)
          | (have i₁ := b1e216313 x y
             have i₂ := b1e218438 X0
             grind)
          | exact superpose b1e218438 b1e216313
          | (have j0 := b1e216313 x y
             have j1 := b1e218438 x
             grind)
          | exact resolve b1e216313 b1e218438
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e216313 b1e218438
        have b1e223282 : ∀ X0 : G, (M.op X0 x) = (k y X0) ∨ (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e222904 X0
             grind)
          | (have r₁ := b1e222904 X0
             have r₂ := b1e367
             grind)
          | exact resolve b1e222904 b1e367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e222904
        have b1e224022 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op (τ (M.op (σ x) X0)) x) ∨ (M.op (τ (M.op (σ x) X0)) x) = (k x (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b1e18936 X0
             have i₂ := b1e223282 (τ (M.op (σ x) X0))
             grind)
          | exact superpose b1e223282 b1e18936
          | (have j1 := b1e223282 (τ (M.op (σ x) X0))
             grind)
          | exact resolve b1e18936 b1e223282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18936 b1e223282
        have b1e224140 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op (τ (M.op (σ x) X0)) x) ∨ (τ (M.op (σ x) X0)) = (M.op (τ (M.op (σ x) X0)) x) := by
          intro X0
          first
          | (have i₁ := b1e224022 X0
             have i₂ := b1e18630 x X0
             grind)
          | exact superpose b1e18630 b1e224022
          | (have j0 := b1e224022 X0
             grind)
          | exact resolve b1e224022 b1e18630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18630 b1e224022
        have b1e224141 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op (τ (M.op (σ x) X0)) x) := by
          intro X0
          first
          | (have j0 := b1e224140 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e224140
        have b1e224730 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (τ (M.op (σ x) X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 x X1 (τ (M.op (σ x) X0))
             have i₂ := b1e224141 X0
             grind)
          | exact superpose b1e224141 b1e30
          | exact resolve b1e30 b1e224141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e224141
        have b1e230389 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e3828 X0 (σ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e3828
          | exact resolve b1e3828 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3828
        have b1e231736 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e230389 X0 X1
             have i₂ := b1e103 X0
             grind)
          | exact superpose b1e103 b1e230389
          | (have j0 := b1e230389 X0 X1
             grind)
          | exact resolve b1e230389 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103 b1e230389
        have b1e241360 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op X0 x)) ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e231736 y X0
             have i₂ := b1e31 X0
             grind)
          | exact superpose b1e31 b1e231736
          | (have j0 := b1e231736 y X0
             grind)
          | exact resolve b1e231736 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e242371 : ∀ X0 : G, (σ (M.op y x)) = (σ (M.op X0 x)) ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e241360 X0
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e241360
          | (have j0 := b1e241360 X0
             grind)
          | exact resolve b1e241360 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e241360
        have b1e246242 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op X0 x)) ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e367
             have i₂ := b1e242371 X0
             grind)
          | (have i₁ := b1e367
             have i₂ := b1e242371 y
             grind)
          | exact superpose b1e242371 b1e367
          | (have j1 := b1e242371 X0
             grind)
          | (have r₁ := b1e367
             have r₂ := b1e242371 x
             grind)
          | exact resolve b1e367 b1e242371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e367 b1e242371
        have b1e248119 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k X0 y) = (M.op y X0) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e246242 X0
             have i₂ := b1e231736 x X0
             grind)
          | (have i₁ := b1e246242 x
             have i₂ := b1e231736 x x
             grind)
          | exact superpose b1e231736 b1e246242
          | (have j0 := b1e246242 x
             have j1 := b1e231736 y X0
             grind)
          | (have r₁ := b1e246242 x
             have r₂ := b1e231736 x x
             grind)
          | (have r₁ := b1e246242 x
             have r₂ := b1e231736 x x
             grind)
          | exact resolve b1e246242 b1e231736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e231736 b1e246242
        have b1e248127 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e248119 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248119
        have b1e248491 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) ∨ (M.op y X0) = (M.op y y) ∨ (k (M.op y X0) x) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e1384 y X0
             have i₂ := b1e248127 (M.op y X0)
             grind)
          | exact superpose b1e248127 b1e1384
          | (have j0 := b1e1384 y (M.op y X0)
             have j1 := b1e248127 (M.op y X0)
             grind)
          | exact resolve b1e1384 b1e248127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1384 b1e248127
        have b1e248587 : ∀ X0 : G, (M.op y X0) = (M.op y y) ∨ (M.op y X0) = (M.op y y) ∨ (k (M.op y X0) x) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e248491 X0
             have i₂ := b1e30 X0 y y
             grind)
          | exact superpose b1e30 b1e248491
          | (have j0 := b1e248491 X0
             grind)
          | exact resolve b1e248491 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248491
        have b1e248588 : ∀ X0 : G, (M.op y X0) = (M.op y y) ∨ (k (M.op y X0) x) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have j0 := b1e248587 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248587
        have b1e248656 : ∀ X0 : G, (M.op y X0) = (M.op y x) ∨ (k (M.op y X0) x) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e248588 X0
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e248588
          | (have j0 := b1e248588 X0
             grind)
          | exact resolve b1e248588 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248588
        have b1e248698 : ∀ X0 : G, (M.op x X0) = (k (M.op y X0) x) ∨ (M.op y X0) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b1e248656 X0
             have i₂ := b1e30 X0 x y
             grind)
          | exact superpose b1e30 b1e248656
          | (have j0 := b1e248656 X0
             grind)
          | exact resolve b1e248656 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248656
        have b1e248725 : ∀ X0 : G, (M.op x X0) = (k (M.op y X0) x) := by
          intro X0
          first
          | (have j0 := b1e248698 X0
             have j1 := b1e95 y X0 x
             grind)
          | (have r₁ := b1e248698 x
             have r₂ := b1e95 y x x
             grind)
          | (have r₁ := b1e248698 x
             have r₂ := b1e95 y x x
             grind)
          | exact resolve b1e248698 b1e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e95 b1e248698
        have b1e292169 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (τ (σ (M.op X0 X0)))) ∨ (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e224730 (σ X0) X1
             have i₂ := b1e12638 X0
             grind)
          | exact superpose b1e12638 b1e224730
          | (have j1 := b1e12638 X0
             grind)
          | exact resolve b1e224730 b1e12638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12638 b1e224730
        have b1e292689 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op X0 X0)) ∨ (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e292169 X0 X1
             have i₂ := b1e13 (M.op X0 X0)
             grind)
          | exact superpose b1e13 b1e292169
          | (have j0 := b1e292169 X0 X1
             grind)
          | exact resolve b1e292169 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e292169
        have b1e293022 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 x) ∨ (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e292689 X0 X1
             have i₂ := b1e30 X0 X1 X0
             grind)
          | exact superpose b1e30 b1e292689
          | (have j0 := b1e292689 X0 X1
             grind)
          | exact resolve b1e292689 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e292689
        have b1e301368 : ∀ X0 X1 : G, (k X0 y) = (τ (σ (k X0 x))) ∨ (M.op X1 X0) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 y)
             have i₂ := b1e293022 X0 X1
             grind)
          | exact superpose b1e293022 b1e13
          | (have j1 := b1e293022 X0 X1
             grind)
          | exact resolve b1e13 b1e293022
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e293022
        have b1e301599 : ∀ X0 X1 : G, (k X0 y) = (k X0 x) ∨ (M.op X1 X0) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e301368 X0 X1
             have i₂ := b1e13 (k X0 x)
             grind)
          | exact superpose b1e13 b1e301368
          | (have j0 := b1e301368 X0 X1
             grind)
          | exact resolve b1e301368 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e301368
        have b1e302778 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y X0) x) ∨ (M.op X1 x) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e8140 y X0
             have i₂ := b1e301599 (M.op y X0) X1
             grind)
          | exact superpose b1e301599 b1e8140
          | (have j1 := b1e301599 (M.op y X0) X1
             grind)
          | exact resolve b1e8140 b1e301599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e302857 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (k X0 y) = (M.op y X0) ∨ (k X0 y) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e76 X0
             have i₂ := b1e301599 X0 X0
             grind)
          | (have i₁ := b1e76 x
             have i₂ := b1e301599 X0 x
             grind)
          | exact superpose b1e301599 b1e76
          | (have j0 := b1e76 X0
             have j1 := b1e301599 X0 x
             grind)
          | (have r₁ := b1e76 X0
             have r₂ := b1e301599 X0 X0
             grind)
          | (have r₁ := b1e76 x
             have r₂ := b1e301599 x x
             grind)
          | exact resolve b1e76 b1e301599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e301599
        have b1e303871 : ∀ X0 : G, (k X0 y) = (k X0 x) ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b1e302857 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e302857
        have b1e304005 : ∀ X0 X1 : G, (M.op x X0) = (M.op y y) ∨ (M.op X1 x) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e302778 X0 X1
             have i₂ := b1e248725 X0
             grind)
          | exact superpose b1e248725 b1e302778
          | (have j0 := b1e302778 X0 X1
             grind)
          | exact resolve b1e302778 b1e248725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e302778
        have b1e304131 : ∀ X0 X1 : G, (M.op x X0) = (M.op y x) ∨ (M.op X1 x) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e304005 X0 X1
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e304005
          | (have j0 := b1e304005 X0 X1
             grind)
          | exact resolve b1e304005 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304005
        have b1e304170 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 x) ∨ (M.op x X0) = (M.op y x) := by
          intro X0 X1
          first
          | (have i₁ := b1e304131 X0 X1
             have i₂ := b1e30 X0 X1 y
             grind)
          | exact superpose b1e30 b1e304131
          | (have j0 := b1e304131 X0 X1
             grind)
          | exact resolve b1e304131 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304131
        have b1e304376 : ∀ X0 : G, (M.op y X0) ≠ (k X0 x) ∨ (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b1e303871 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e303871
        have b1e307063 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op x X0) X1) ∨ (M.op X2 X0) = (M.op X2 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 y x X1
             have i₂ := b1e304170 X0 X2
             grind)
          | exact superpose b1e304170 b1e32
          | (have j1 := b1e304170 X0 X2
             grind)
          | exact resolve b1e32 b1e304170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304170
        have b1e307301 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op x X1) ∨ (M.op X2 X0) = (M.op X2 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e307063 X0 X1 X2
             have i₂ := b1e32 x X0 X1
             grind)
          | exact superpose b1e32 b1e307063
          | (have j0 := b1e307063 X0 X1 X2
             grind)
          | exact resolve b1e307063 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e307063
        have b1e307886 : ∀ X0 : G, (M.op x X0) ≠ (M.op y (M.op y X0)) ∨ (M.op y (M.op y X0)) = (k (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b1e304376 (M.op y X0)
             have i₂ := b1e248725 X0
             grind)
          | exact superpose b1e248725 b1e304376
          | (have j0 := b1e304376 (M.op y X0)
             grind)
          | exact resolve b1e304376 b1e248725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248725 b1e304376
        have b1e307977 : ∀ X0 : G, (M.op x X0) ≠ (M.op y X0) ∨ (M.op y (M.op y X0)) = (k (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b1e307886 X0
             have i₂ := b1e30 X0 y y
             grind)
          | exact superpose b1e30 b1e307886
          | (have j0 := b1e307886 X0
             grind)
          | exact resolve b1e307886 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e307886
        have b1e308007 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) ∨ (M.op x X0) ≠ (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e307977 X0
             have i₂ := b1e8140 y X0
             grind)
          | exact superpose b1e8140 b1e307977
          | (have j0 := b1e307977 X0
             grind)
          | exact resolve b1e307977 b1e8140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8140 b1e307977
        have b1e308013 : ∀ X0 : G, (M.op y X0) = (M.op y y) ∨ (M.op x X0) ≠ (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e308007 X0
             have i₂ := b1e30 X0 y y
             grind)
          | exact superpose b1e30 b1e308007
          | (have j0 := b1e308007 X0
             grind)
          | exact resolve b1e308007 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e308007
        have b1e308018 : ∀ X0 : G, (M.op y X0) = (M.op y x) ∨ (M.op x X0) ≠ (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e308013 X0
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e308013
          | (have j0 := b1e308013 X0
             grind)
          | exact resolve b1e308013 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e308013
        have b1e308023 : ∀ X0 : G, (M.op y X0) = (M.op y x) := by
          intro X0
          first
          | (have j0 := b1e308018 X0
             have j1 := b1e307301 X0 x y
             grind)
          | (have r₁ := b1e308018 x
             have r₂ := b1e307301 X0 x x
             grind)
          | exact resolve b1e308018 b1e307301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e307301 b1e308018
        have b1e308351 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e308023 X0
             have i₂ := b1e308023 X1
             grind)
          | (have i₁ := b1e308023 X0
             have i₂ := b1e308023 x
             grind)
          | exact superpose b1e308023 b1e308023
          | exact resolve b1e308023 b1e308023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e308849 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 x X1 y
             have i₂ := b1e308023 X0
             grind)
          | (have i₁ := b1e30 X0 x y
             have i₂ := b1e308023 X0
             grind)
          | exact superpose b1e308023 b1e30
          | exact resolve b1e30 b1e308023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e308023
        have b1e309103 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e308849 X0 X1
             have i₂ := b1e30 X0 X1 y
             grind)
          | exact superpose b1e30 b1e308849
          | exact resolve b1e308849 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e308849
        have b1e311863 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e30 X2 X1 y
             have i₂ := b1e308351 X2 X0
             grind)
          | (have i₁ := b1e30 X2 X1 y
             have i₂ := b1e308351 X0 X2
             grind)
          | exact superpose b1e308351 b1e30
          | exact resolve b1e30 b1e308351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e308351
        have b1e312247 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e311863 X2 X1 X0
             have i₂ := b1e30 X2 X1 y
             grind)
          | exact superpose b1e30 b1e311863
          | exact resolve b1e311863 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e311863
        have b1e317324 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) x) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e309103 (σ y) (σ x)
             grind)
          | exact superpose b1e309103 b1e21
          | exact resolve b1e21 b1e309103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e309103
        have b1e318125 : False := by grind
        exact b1e318125
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e28 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) (M.op x x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y X1 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e28 X0 x
             have i₂ := b2e12 X0 x x x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e77 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 y) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b2e15 y X0
             have i₂ := b2e31 y
             grind)
          | exact superpose b2e31 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e31 x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e31 y
             grind)
          | exact resolve b2e15 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e79 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e82 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b2e77 X0
             have i₂ := b2e31 X0
             grind)
          | exact superpose b2e31 b2e77
          | (have j0 := b2e77 X0
             grind)
          | (have r₁ := b2e77 y
             have r₂ := b2e31 y
             grind)
          | exact resolve b2e77 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e77
        have b2e96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e79 (σ X0)
             grind)
          | exact superpose b2e79 b2e18
          | exact resolve b2e18 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e96 X0
             have i₂ := b2e79 X0
             grind)
          | exact superpose b2e79 b2e96
          | exact resolve b2e96 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79 b2e96
        have b2e187 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e187 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e197 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e196 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e196
        have b2e208 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e197 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e197 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e197 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e197 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e197
        have b2e482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e208 (σ X0) (σ X1)
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e208
          | exact resolve b2e208 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e208
        have b2e3669 : (M.op x x) = (k y x) := by
          first
          | (have j0 := b2e82 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e12220 : (M.op (σ x) (σ x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e482 y x
             grind)
          | exact superpose b2e482 b2e22
          | (have j1 := b2e482 y x
             grind)
          | exact resolve b2e22 b2e482
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482
        have b2e12351 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e12220
             have i₂ := b2e3669
             grind)
          | exact superpose b2e3669 b2e12220
          | exact resolve b2e12220 b2e3669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12220
        have b2e12438 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e12351
             have r₂ := b2e97 x
             grind)
          | exact resolve b2e12351 b2e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e97 b2e12351
        have b2e12470 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e12438
             have i₂ := b2e3669
             grind)
          | exact superpose b2e3669 b2e12438
          | exact resolve b2e12438 b2e3669
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3669 b2e12438
        have b2e12481 : False := by grind
        exact b2e12481
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e24 X0 X1
             grind)
          | exact superpose b3e24 b3e13
          | exact resolve b3e13 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e30 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x x) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 y X0 x X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
          intro X0 X1 X2 X3 X5
          first
          | (have i₁ := b3e12 (M.op X0 X2) X3 (M.op x X1) X5
             have i₂ := b3e12 X0 X1 X2 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b3e12 X0 X1 x X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e33 x X1 X2 X3 x
             have i₂ := b3e12 X2 X1 x x
             grind)
          | exact superpose b3e12 b3e33
          | exact resolve b3e33 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e35 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e31 X0 x X2 X3 x
             have i₂ := b3e12 X0 X3 x x
             grind)
          | exact superpose b3e12 b3e31
          | exact resolve b3e31 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e36 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e30 X0 x
             have i₂ := b3e12 x X0 x x
             grind)
          | exact superpose b3e12 b3e30
          | exact resolve b3e30 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e40 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X1) (M.op (σ x) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ y) X1 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e40 X0 x
             have i₂ := b3e12 X0 (σ x) x (σ x)
             grind)
          | exact superpose b3e12 b3e40
          | exact resolve b3e40 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X2 X1)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 X0 (M.op X2 X1)
             have i₂ := b3e34 X1 X0 X2
             grind)
          | exact superpose b3e34 b3e15
          | (have j0 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e15 X1 (M.op x X1)
             have r₂ := b3e34 X1 X1 x
             grind)
          | (have r₁ := b3e15 (M.op x X1) X1
             have r₂ := b3e34 X1 (M.op x X1) x
             grind)
          | exact resolve b3e15 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : ∀ X0 : G, (M.op x y) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e15 y X0
             have i₂ := b3e36 y
             grind)
          | exact superpose b3e36 b3e15
          | (have j0 := b3e15 y X0
             grind)
          | exact resolve b3e15 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e69 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e66 X0
             have i₂ := b3e36 X0
             grind)
          | exact superpose b3e36 b3e66
          | (have j0 := b3e66 X0
             grind)
          | (have r₁ := b3e66 y
             have r₂ := b3e36 y
             grind)
          | exact resolve b3e66 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e75 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X2 X1)) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e60 X0 X1 X2
             have i₂ := b3e35 X2 X1 X0
             grind)
          | exact superpose b3e35 b3e60
          | (have j0 := b3e60 X0 X1 X2
             grind)
          | exact resolve b3e60 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e81 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e67 (σ X0)
             grind)
          | exact superpose b3e67 b3e18
          | exact resolve b3e18 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e81 X0
             have i₂ := b3e67 X0
             grind)
          | exact superpose b3e67 b3e81
          | exact resolve b3e81 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67 b3e81
        have b3e88 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 (M.op x X1) X1
             have i₂ := b3e12 x X1 X1 x
             grind)
          | exact superpose b3e12 b3e16
          | (have j0 := b3e16 (M.op X0 X1) X2
             grind)
          | exact resolve b3e16 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e100 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e88 X0 X1 X2
             have i₂ := b3e34 X1 X2 X0
             grind)
          | exact superpose b3e34 b3e88
          | (have j0 := b3e88 X0 X1 X2
             grind)
          | (have r₁ := b3e88 x X1 x
             have r₂ := b3e34 X1 x x
             grind)
          | exact resolve b3e88 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e105 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e100 X0 X1 X2
             have i₂ := b3e35 X0 X1 X2
             grind)
          | exact superpose b3e35 b3e100
          | (have j0 := b3e100 X0 X1 X2
             grind)
          | (have r₁ := b3e100 X0 x (M.op X0 X2)
             have r₂ := b3e35 X0 X2 x
             grind)
          | (have r₁ := b3e100 (M.op X0 X2) x X0
             have r₂ := b3e35 X0 X2 x
             grind)
          | exact resolve b3e100 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e100
        have b3e109 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e105 X0 X1 X2
             have i₂ := b3e35 X0 X1 X2
             grind)
          | exact superpose b3e35 b3e105
          | (have j0 := b3e105 X0 X1 X2
             grind)
          | (have r₁ := b3e105 X0 x (M.op X0 X2)
             have r₂ := b3e35 X0 X2 x
             grind)
          | (have r₁ := b3e105 (M.op X0 X2) x X0
             have r₂ := b3e35 X0 X2 x
             grind)
          | exact resolve b3e105 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105
        have b3e134 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X0
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e156 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e23
             have i₂ := b3e17 (σ x) X0
             grind)
          | (have i₁ := b3e23
             have i₂ := b3e17 (σ x) (σ x)
             grind)
          | exact superpose b3e17 b3e23
          | (have j1 := b3e17 (σ x) X0
             grind)
          | exact resolve b3e23 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e157 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X3 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X2 X0 X3
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1 X0 X3
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X1
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e160 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e170 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e160 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e160
        have b3e171 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e170 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e170
        have b3e174 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e134 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134
        have b3e175 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e174 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e174
        have b3e181 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e171 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e171 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e171 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e171 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e183 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X3 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b3e157 X0 X1 X2 X3
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e157 X0 (M.op X0 X0) X0 X0
             have r₂ := b3e15 (M.op X0 X0) X0
             grind)
          | (have r₁ := b3e157 X0 (M.op X0 X0) (M.op X0 X0) X3
             have r₂ := b3e15 (M.op X0 X0) (M.op X3 (M.op X0 X0))
             grind)
          | (have r₁ := b3e157 X0 X1 X2 X3
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e157 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157
        have b3e184 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e156 X0
             have j1 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e156 (σ x)
             have r₂ := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e156 x
             have r₂ := b3e15 (σ x) x
             grind)
          | exact resolve b3e156 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e213 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e183 X0 X1 X2 x
             have i₂ := b3e12 X0 X2 X0 x
             grind)
          | exact superpose b3e12 b3e183
          | (have j0 := b3e183 X0 X1 X2 x
             grind)
          | exact resolve b3e183 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e183
        have b3e264 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X1 (M.op X0 X2)
             have i₂ := b3e35 X0 X2 X1
             grind)
          | exact superpose b3e35 b3e16
          | (have j0 := b3e16 X1 (M.op X0 X2)
             grind)
          | (have r₁ := b3e16 x (M.op x X2)
             have r₂ := b3e35 x X2 x
             grind)
          | (have r₁ := b3e16 (M.op X0 X2) X0
             have r₂ := b3e35 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b3e16 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e278 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e264 X0 X1 X2
             have i₂ := b3e34 X2 X1 X0
             grind)
          | exact superpose b3e34 b3e264
          | (have j0 := b3e264 X0 X1 X2
             grind)
          | exact resolve b3e264 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e264
        have b3e294 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e278 X0 X1 X2
             have i₂ := b3e34 X2 X1 X0
             grind)
          | exact superpose b3e34 b3e278
          | (have j0 := b3e278 X0 X1 X2
             grind)
          | exact resolve b3e278 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e278
        have b3e383 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e25 X1 X0
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e429 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e175 (σ X1) (σ X0)
             grind)
          | exact superpose b3e175 b3e18
          | (have j1 := b3e175 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e175
        have b3e474 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e429 X0 X1
             have i₂ := b3e84 X1
             grind)
          | exact superpose b3e84 b3e429
          | (have j0 := b3e429 X0 X1
             grind)
          | exact resolve b3e429 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e429
        have b3e513 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e42 (σ y)
             have i₂ := b3e84 y
             grind)
          | exact superpose b3e84 b3e42
          | exact resolve b3e42 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e530 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e513
             have i₂ := b3e36 y
             grind)
          | exact superpose b3e36 b3e513
          | exact resolve b3e513 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e513
        have b3e603 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e181 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e181
        have b3e665 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X1 X2
             have i₂ := b3e213 X2 X0 X1
             grind)
          | (have i₁ := b3e16 X2 X1
             have i₂ := b3e213 X0 X1 X2
             grind)
          | exact superpose b3e213 b3e16
          | (have j0 := b3e16 X1 X2
             have j1 := b3e213 X2 X0 X2
             grind)
          | (have r₁ := b3e16 X2 X1
             have r₂ := b3e213 X2 X1 X2
             grind)
          | (have r₁ := b3e16 X2 X0
             have r₂ := b3e213 X0 X2 X2
             grind)
          | exact resolve b3e16 b3e213
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e703 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e23
             have i₂ := b3e213 X0 (σ x) (σ x)
             grind)
          | (have i₁ := b3e23
             have i₂ := b3e213 (σ x) x (σ x)
             grind)
          | exact superpose b3e213 b3e23
          | (have j1 := b3e213 X0 (σ x) x
             grind)
          | exact resolve b3e23 b3e213
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e708 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) ∨ (M.op y X0) = (k X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e36 X1
             have i₂ := b3e213 X0 y X1
             grind)
          | (have i₁ := b3e36 x
             have i₂ := b3e213 y X1 x
             grind)
          | exact superpose b3e213 b3e36
          | (have j1 := b3e213 X0 x X1
             grind)
          | exact resolve b3e36 b3e213
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e213
        have b3e714 : ∀ X0 X1 : G, (M.op x X0) = (k X0 y) ∨ (M.op X0 X1) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e708 X0 X1
             have i₂ := b3e36 X0
             grind)
          | exact superpose b3e36 b3e708
          | (have j0 := b3e708 X0 X1
             grind)
          | exact resolve b3e708 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e708
        have b3e983 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e184 (M.op X0 x)
             have i₂ := b3e35 X0 x (σ x)
             grind)
          | exact superpose b3e35 b3e184
          | (have j0 := b3e184 X0
             grind)
          | exact resolve b3e184 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e184
        have b3e2230 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e109 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e109
        have b3e4718 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op X0 X1) = (k X0 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e603 X2 (M.op x X1)
             have i₂ := b3e34 X1 X2 x
             grind)
          | exact superpose b3e34 b3e603
          | exact resolve b3e603 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4724 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e603 (M.op X0 X2) x
             have i₂ := b3e35 X0 X2 x
             grind)
          | exact superpose b3e35 b3e603
          | exact resolve b3e603 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4808 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X0 X1) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e4724 X0 X1 X2
             have i₂ := b3e34 X2 X1 X0
             grind)
          | exact superpose b3e34 b3e4724
          | (have j0 := b3e4724 X0 X1 X2
             grind)
          | (have r₁ := b3e4724 x x x
             have r₂ := b3e34 x x x
             grind)
          | exact resolve b3e4724 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4724
        have b3e4813 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e4718 X0 X1 X2
             have i₂ := b3e35 X2 X1 X0
             grind)
          | exact superpose b3e35 b3e4718
          | (have j0 := b3e4718 X0 X1 X2
             grind)
          | (have r₁ := b3e4718 X2 X2 X2
             have r₂ := b3e35 X2 X2 X2
             grind)
          | exact resolve b3e4718 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4718
        have b3e5751 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op x X1) = (k X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e603 X0 X1
             have i₂ := b3e714 X1 X0
             grind)
          | (have i₁ := b3e603 X1 x
             have i₂ := b3e714 X0 X1
             grind)
          | exact superpose b3e714 b3e603
          | (have j0 := b3e603 X0 X1
             have j1 := b3e714 X1 X1
             grind)
          | (have r₁ := b3e603 x x
             have r₂ := b3e714 x x
             grind)
          | exact resolve b3e603 b3e714
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e603 b3e714
        have b3e7765 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e75 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e10544 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e2230 x (M.op x X1)
             have i₂ := b3e34 X1 x x
             grind)
          | exact superpose b3e34 b3e2230
          | (have j0 := b3e2230 X0 X1
             grind)
          | exact resolve b3e2230 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2230
        have b3e10630 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b3e10544 X0 X1
             have j1 := b3e4808 X0 X0 X1
             grind)
          | (have r₁ := b3e10544 x x
             have r₂ := b3e4808 x x x
             grind)
          | (have r₁ := b3e10544 X0 x
             have r₂ := b3e4808 X0 X0 x
             grind)
          | exact resolve b3e10544 b3e4808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4808 b3e10544
        have b3e10770 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 (M.op (σ X0) X1) X0
             have i₂ := b3e10630 (σ X0) X1
             grind)
          | exact superpose b3e10630 b3e29
          | exact resolve b3e29 b3e10630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10630
        have b3e10775 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e10770 X0 X1
             have i₂ := b3e84 X0
             grind)
          | exact superpose b3e84 b3e10770
          | exact resolve b3e10770 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84 b3e10770
        have b3e10808 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (σ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e10775 X0 X1
             have i₂ := b3e13 (M.op X0 X0)
             grind)
          | exact superpose b3e13 b3e10775
          | exact resolve b3e10775 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10775
        have b3e12601 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (k (M.op X0 X1) (σ x)) = (M.op (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e703 (M.op X0 X1)
             have i₂ := b3e35 X0 X1 (σ x)
             grind)
          | exact superpose b3e35 b3e703
          | (have j0 := b3e703 X0
             grind)
          | exact resolve b3e703 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e703
        have b3e12624 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X1) = (k (M.op X0 X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12601 X0 X1
             have i₂ := b3e34 X1 (σ x) X0
             grind)
          | exact superpose b3e34 b3e12601
          | (have j0 := b3e12601 X0 X1
             grind)
          | exact resolve b3e12601 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12601
        have b3e20831 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e983 (σ y) x
             have i₂ := b3e530
             grind)
          | exact superpose b3e530 b3e983
          | (have r₁ := b3e983 (σ y) x
             have r₂ := b3e530
             grind)
          | exact resolve b3e983 b3e530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e983
        have b3e20849 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have j0 := b3e20831 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20831
        have b3e20914 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e383 x (M.op (σ y) X0)
             have i₂ := b3e20849 X0
             grind)
          | exact superpose b3e20849 b3e383
          | exact resolve b3e383 b3e20849
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20849
        have b3e20932 : ∀ X0 : G, (M.op x y) = (k x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e20914 X0
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e20914
          | exact resolve b3e20914 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20914
        have b3e41667 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e294 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e294
        have b3e41694 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e41667 X0 X1
             have j1 := b3e4813 X0 X1 X0
             grind)
          | (have r₁ := b3e41667 x X1
             have r₂ := b3e4813 x X1 x
             grind)
          | (have r₁ := b3e41667 X1 X1
             have r₂ := b3e4813 X1 X1 X1
             grind)
          | exact resolve b3e41667 b3e4813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4813 b3e41667
        have b3e42109 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (σ X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e383 X0 (M.op (σ X0) X1)
             have i₂ := b3e41694 (σ X0) X1
             grind)
          | exact superpose b3e41694 b3e383
          | exact resolve b3e383 b3e41694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e383 b3e41694
        have b3e73344 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k x X0) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e665 y x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e665
          | (have j0 := b3e665 x x X0
             grind)
          | (have r₁ := b3e665 y x x
             have r₂ := b3e21
             grind)
          | exact resolve b3e665 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e665
        have b3e73428 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k x X0) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e73344 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73344
        have b3e73485 : ∀ X0 : G, (M.op x X0) = (k X0 y) ∨ (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e73428 X0
             have i₂ := b3e36 X0
             grind)
          | exact superpose b3e36 b3e73428
          | (have j0 := b3e73428 X0
             grind)
          | exact resolve b3e73428 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73428
        have b3e73569 : ∀ X0 : G, (M.op x X0) = (k X0 y) ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b3e73485 X0
             have j1 := b3e5751 x X0
             grind)
          | (have r₁ := b3e73485 x
             have r₂ := b3e5751 x x
             grind)
          | (have r₁ := b3e73485 x
             have r₂ := b3e5751 x x
             grind)
          | exact resolve b3e73485 b3e5751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5751 b3e73485
        have b3e75511 : ∀ X0 : G, (M.op y y) = (M.op x (τ (M.op (σ y) X0))) ∨ (M.op x (τ (M.op (σ y) X0))) = (k x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e10808 y X0
             have i₂ := b3e73569 (τ (M.op (σ y) X0))
             grind)
          | exact superpose b3e73569 b3e10808
          | (have j1 := b3e73569 (τ (M.op (σ y) X0))
             grind)
          | exact resolve b3e10808 b3e73569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75558 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op (σ y) X0))) ∨ (M.op x (τ (M.op (σ y) X0))) = (k x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e75511 X0
             have i₂ := b3e36 y
             grind)
          | exact superpose b3e36 b3e75511
          | (have j0 := b3e75511 X0
             grind)
          | exact resolve b3e75511 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e75511
        have b3e75614 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op (σ y) X0))) ∨ (M.op x y) = (M.op x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e75558 X0
             have i₂ := b3e20932 X0
             grind)
          | exact superpose b3e20932 b3e75558
          | (have j0 := b3e75558 X0
             grind)
          | exact resolve b3e75558 b3e20932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e20932 b3e75558
        have b3e75615 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have j0 := b3e75614 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75614
        have b3e76271 : ∀ X0 : G, (M.op x y) = (M.op x (τ (σ (M.op X0 X0)))) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e75615 (σ X0)
             have i₂ := b3e474 y X0
             grind)
          | exact superpose b3e474 b3e75615
          | (have j1 := b3e474 y X0
             grind)
          | exact resolve b3e75615 b3e474
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e474
        have b3e76342 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op (τ (M.op (σ y) X0)) y) = (k y (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e69 (τ (M.op (σ y) X0))
             have i₂ := b3e75615 X0
             grind)
          | exact superpose b3e75615 b3e69
          | (have j0 := b3e69 y
             grind)
          | (have r₁ := b3e69 (τ (M.op (σ y) X0))
             have r₂ := b3e75615 X0
             grind)
          | exact resolve b3e69 b3e75615
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69 b3e75615
        have b3e76453 : ∀ X0 : G, (M.op (τ (M.op (σ y) X0)) y) = (k y (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have j0 := b3e76342 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76342
        have b3e76470 : ∀ X0 : G, (τ (M.op (σ y) X0)) = (M.op (τ (M.op (σ y) X0)) y) := by
          intro X0
          first
          | (have i₁ := b3e76453 X0
             have i₂ := b3e42109 y X0
             grind)
          | exact superpose b3e42109 b3e76453
          | exact resolve b3e76453 b3e42109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42109 b3e76453
        have b3e76494 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 X0)) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e76271 X0
             have i₂ := b3e13 (M.op X0 X0)
             grind)
          | exact superpose b3e13 b3e76271
          | (have j0 := b3e76271 X0
             grind)
          | exact resolve b3e76271 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76271
        have b3e76515 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k X0 y)) ∨ (M.op x y) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e76494 X0
             have i₂ := b3e34 X0 x X0
             grind)
          | exact superpose b3e34 b3e76494
          | (have j0 := b3e76494 X0
             grind)
          | exact resolve b3e76494 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76494
        have b3e334314 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) X0) = (k (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12624 (σ y) X0
             have i₂ := b3e530
             grind)
          | exact superpose b3e530 b3e12624
          | (have j0 := b3e12624 (σ y) X0
             grind)
          | (have r₁ := b3e12624 (σ y) x
             have r₂ := b3e530
             grind)
          | exact resolve b3e12624 b3e530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e530 b3e12624
        have b3e334320 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b3e334314 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e334314
        have b3e334419 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k (τ (M.op (σ y) X0)) x) := by
          intro X0
          first
          | (have i₁ := b3e29 (M.op (σ y) X0) x
             have i₂ := b3e334320 X0
             grind)
          | exact superpose b3e334320 b3e29
          | exact resolve b3e29 b3e334320
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e334320
        have b3e341058 : ∀ X0 : G, (τ (σ (k X0 y))) = (M.op (τ (σ (k X0 y))) y) ∨ (M.op x y) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e76470 (σ X0)
             have i₂ := b3e76515 X0
             grind)
          | exact superpose b3e76515 b3e76470
          | (have j1 := b3e76515 X0
             grind)
          | exact resolve b3e76470 b3e76515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76515
        have b3e341144 : ∀ X0 : G, (k X0 y) = (M.op (k X0 y) y) ∨ (M.op x y) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e341058 X0
             have i₂ := b3e13 (k X0 y)
             grind)
          | exact superpose b3e13 b3e341058
          | (have j0 := b3e341058 X0
             grind)
          | exact resolve b3e341058 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341058
        have b3e341431 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) y) ∨ (M.op x y) = (M.op x X0) ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e341144 X0
             have i₂ := b3e73569 X0
             grind)
          | exact superpose b3e73569 b3e341144
          | (have j0 := b3e341144 X0
             have j1 := b3e73569 X0
             grind)
          | exact resolve b3e341144 b3e73569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73569 b3e341144
        have b3e341497 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (M.op x y) = (M.op x X0) ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e341431 X0
             have i₂ := b3e35 x X0 y
             grind)
          | exact superpose b3e35 b3e341431
          | (have j0 := b3e341431 X0
             grind)
          | exact resolve b3e341431 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341431
        have b3e341498 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op x y) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b3e341497 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341497
        have b3e341683 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op X0 x)) ∨ (M.op x y) = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e7765 x X0
             have i₂ := b3e341498 (M.op X0 x)
             grind)
          | exact superpose b3e341498 b3e7765
          | (have j1 := b3e341498 (M.op X0 x)
             grind)
          | exact resolve b3e7765 b3e341498
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7765 b3e341498
        have b3e341702 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (M.op x y) = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e341683 X0
             have i₂ := b3e34 x x X0
             grind)
          | exact superpose b3e34 b3e341683
          | (have j0 := b3e341683 X0
             grind)
          | exact resolve b3e341683 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341683
        have b3e341706 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e341702 X0
             have i₂ := b3e34 x x X0
             grind)
          | exact superpose b3e34 b3e341702
          | (have j0 := b3e341702 X0
             grind)
          | exact resolve b3e341702 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e341702
        have b3e341708 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b3e341706 X0
             grind)
          | (have r₁ := b3e341706 X0
             have r₂ := b3e20
             grind)
          | exact resolve b3e341706 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341706
        have b3e341736 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b3e341708 X1
             have i₂ := b3e341708 X0
             grind)
          | (have i₁ := b3e341708 X0
             have i₂ := b3e341708 x
             grind)
          | exact superpose b3e341708 b3e341708
          | exact resolve b3e341708 b3e341708
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e342021 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e35 X0 x X1
             have i₂ := b3e341708 X0
             grind)
          | (have i₁ := b3e35 x x x
             have i₂ := b3e341708 X0
             grind)
          | exact superpose b3e341708 b3e35
          | exact resolve b3e35 b3e341708
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e341708
        have b3e342310 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e342021 X0 X1
             have i₂ := b3e35 x x X1
             grind)
          | exact superpose b3e35 b3e342021
          | exact resolve b3e342021 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e342021
        have b3e342752 : ∀ X0 : G, (τ (M.op (σ x) x)) = (k (τ (M.op X0 x)) x) := by
          intro X0
          first
          | (have i₁ := b3e334419 x
             have i₂ := b3e341736 (σ y) X0
             grind)
          | (have i₁ := b3e334419 x
             have i₂ := b3e341736 X0 (σ y)
             grind)
          | exact superpose b3e341736 b3e334419
          | exact resolve b3e334419 b3e341736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e334419
        have b3e343121 : ∀ X0 : G, (τ (M.op X0 x)) = (M.op (τ (M.op X0 x)) y) := by
          intro X0
          first
          | (have i₁ := b3e76470 x
             have i₂ := b3e341736 (σ y) x
             grind)
          | (have i₁ := b3e76470 x
             have i₂ := b3e341736 X0 (σ y)
             grind)
          | exact superpose b3e341736 b3e76470
          | exact resolve b3e76470 b3e341736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76470
        have b3e343146 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ (M.op X0 x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e10808 X1 x
             have i₂ := b3e341736 (σ X1) X0
             grind)
          | (have i₁ := b3e10808 X1 x
             have i₂ := b3e341736 X0 (σ X1)
             grind)
          | exact superpose b3e341736 b3e10808
          | exact resolve b3e10808 b3e341736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10808 b3e341736
        have b3e343250 : ∀ X0 : G, (M.op x y) = (τ (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e343121 X0
             have i₂ := b3e342310 (τ (M.op X0 x)) y
             grind)
          | exact superpose b3e342310 b3e343121
          | exact resolve b3e343121 b3e342310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e342310 b3e343121
        have b3e343316 : (M.op x x) = (τ (M.op (σ x) x)) := by
          first
          | (have i₁ := b3e342752 x
             have i₂ := b3e343146 x x
             grind)
          | exact superpose b3e343146 b3e342752
          | exact resolve b3e342752 b3e343146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e342752 b3e343146
        have b3e343405 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e343316
             have i₂ := b3e343250 (σ x)
             grind)
          | exact superpose b3e343250 b3e343316
          | exact resolve b3e343316 b3e343250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e343250 b3e343316
        have b3e343423 : False := by grind
        exact b3e343423
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b4e22 : (M.op x x) = (M.op y x) := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e119 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e120 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
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
          have b4e123 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          clear b4e120
          have b4e124 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e119
          have b4e125 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e123
               have r₂ := b4e21
               grind)
            | exact resolve b4e123 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123
          have b4e126 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e124
               have r₂ := b4e23
               grind)
            | exact resolve b4e124 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e134 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e126
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e126
            | exact resolve b4e126 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126
          have b4e142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e134
               have i₂ := b4e125
               grind)
            | exact superpose b4e125 b4e134
            | exact resolve b4e134 b4e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125 b4e134
          have b4e148 : False := by grind
          exact b4e148
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : (M.op x x) = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x x) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 x X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e31 X0 x
               have i₂ := b5e13 x X0 x x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e100 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e83 (σ X0)
               grind)
            | exact superpose b5e83 b5e19
            | exact resolve b5e19 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e100 X0
               have i₂ := b5e83 X0
               grind)
            | exact superpose b5e83 b5e100
            | exact resolve b5e100 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e100
          have b5e166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b5e196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e208 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e196 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e196
          have b5e209 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e208 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e208
          have b5e212 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e166 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166
          have b5e213 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e212 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e212
          have b5e221 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e209 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e209 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e209 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e209 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e209
          have b5e329 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e213 (σ X1) (σ X0)
               grind)
            | exact superpose b5e213 b5e19
            | (have j1 := b5e213 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213
          have b5e369 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e329 X0 X1
               have i₂ := b5e103 X1
               grind)
            | exact superpose b5e103 b5e329
            | (have j0 := b5e329 X0 X1
               grind)
            | exact resolve b5e329 b5e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e329
          have b5e12499 : (M.op (σ x) (σ x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e369 x y
               grind)
            | exact superpose b5e369 b5e23
            | (have j1 := b5e369 x y
               grind)
            | exact resolve b5e23 b5e369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e12500 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e369 x y
               grind)
            | exact superpose b5e369 b5e20
            | (have j1 := b5e369 x y
               grind)
            | exact resolve b5e20 b5e369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e369
          have b5e12638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e12500
               have i₂ := b5e37 y
               grind)
            | exact superpose b5e37 b5e12500
            | exact resolve b5e12500 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12500
          have b5e12639 : (σ (k y x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e12499
               have i₂ := b5e103 x
               grind)
            | exact superpose b5e103 b5e12499
            | exact resolve b5e12499 b5e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103 b5e12499
          have b5e12767 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b5e12638
               have r₂ := b5e20
               grind)
            | exact resolve b5e12638 b5e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12638
          have b5e12768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e12639
               have i₂ := b5e37 y
               grind)
            | exact superpose b5e37 b5e12639
            | exact resolve b5e12639 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e12639
          have b5e12834 : (σ (k y x)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b5e12768
               have r₂ := b5e20
               grind)
            | exact resolve b5e12768 b5e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12768
          have b5e13435 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e12834
               have i₂ := b5e221 y x
               grind)
            | exact superpose b5e221 b5e12834
            | (have j1 := b5e221 y x
               grind)
            | exact resolve b5e12834 b5e221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e221 b5e12834
          have b5e13439 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e13435
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13435
            | exact resolve b5e13435 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13435
          have b5e13440 : (M.op x y) = (k y x) := by grind
          clear b5e13439
          have b5e13624 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b5e12767
               have i₂ := b5e13440
               grind)
            | exact superpose b5e13440 b5e12767
            | exact resolve b5e12767 b5e13440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12767 b5e13440
          have b5e13625 : False := by grind
          exact b5e13625
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b6e12 X0 X1 x X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b6e31 x X1 X2 X3 x
             have i₂ := b6e12 X2 X1 x x
             grind)
          | exact superpose b6e12 b6e31
          | exact resolve b6e31 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e44 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X1) (M.op (σ x) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (σ y) X1 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e46 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e44 X0 x
             have i₂ := b6e12 X0 (σ x) x (σ x)
             grind)
          | exact superpose b6e12 b6e44
          | exact resolve b6e44 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e66 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b6e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e72 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b6e66
        have b6e77 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e72
          | exact resolve b6e72 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e88 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e71 (σ X0)
             grind)
          | exact superpose b6e71 b6e18
          | exact resolve b6e18 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e88 X0
             have i₂ := b6e71 X0
             grind)
          | exact superpose b6e71 b6e88
          | exact resolve b6e88 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71 b6e88
        have b6e170 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e220 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e170 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e170
        have b6e221 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e220 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e220
        have b6e454 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e46 (σ y)
             have i₂ := b6e91 y
             grind)
          | exact superpose b6e91 b6e46
          | exact resolve b6e46 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e91
        have b6e806 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e454
             grind)
          | exact superpose b6e454 b6e77
          | exact resolve b6e77 b6e454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77 b6e454
        have b6e865 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e806
             grind)
          | exact superpose b6e806 b6e13
          | exact resolve b6e13 b6e806
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e806
        have b6e866 : (k x y) = (M.op y y) := by
          first
          | (have i₁ := b6e865
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e865
          | exact resolve b6e865 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e865
        have b6e921 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b6e221 x y
             have i₂ := b6e866
             grind)
          | exact superpose b6e866 b6e221
          | (have j0 := b6e221 x y
             grind)
          | exact resolve b6e221 b6e866
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e221 b6e866
        have b6e924 : (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b6e921
             have r₂ := b6e21
             grind)
          | exact resolve b6e921 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e921
        have b6e1003 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b6e32 y X0 y
             have i₂ := b6e924
             grind)
          | exact superpose b6e924 b6e32
          | exact resolve b6e32 b6e924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e924
        have b6e1023 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e1003 X0
             have i₂ := b6e32 x X0 y
             grind)
          | exact superpose b6e32 b6e1003
          | exact resolve b6e1003 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e1003
        have b6e1272 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e1023 x
             grind)
          | exact superpose b6e1023 b6e20
          | (have r₁ := b6e20
             have r₂ := b6e1023 x
             grind)
          | exact resolve b6e20 b6e1023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1023
        have b6e1273 : False := by grind
        exact b6e1273
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e32 x X1 X2 X3 x
               have i₂ := b7e13 X2 X1 x x
               grind)
            | exact superpose b7e13 b7e32
            | exact resolve b7e32 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e62 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ y) X0 (σ x) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e62 X0 x
               have i₂ := b7e13 (σ x) X0 (σ x) x
               grind)
            | exact superpose b7e13 b7e62
            | exact resolve b7e62 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e100 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e83 (σ X0)
               grind)
            | exact superpose b7e83 b7e19
            | exact resolve b7e19 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e100 X0
               have i₂ := b7e83 X0
               grind)
            | exact superpose b7e83 b7e100
            | exact resolve b7e100 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e100
          have b7e114 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e116 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e114
          have b7e117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e116
               have r₂ := b7e23
               grind)
            | exact resolve b7e116 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116
          have b7e125 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e117
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e117
            | exact resolve b7e117 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e117
          have b7e182 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e231 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e182 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e182
          have b7e232 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e231 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e231
          have b7e703 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e63 (σ y)
               have i₂ := b7e103 y
               grind)
            | exact superpose b7e103 b7e63
            | exact resolve b7e63 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e103
          have b7e1130 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e125
               have i₂ := b7e703
               grind)
            | exact superpose b7e703 b7e125
            | exact resolve b7e125 b7e703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e703
          have b7e1243 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1130
               grind)
            | exact superpose b7e1130 b7e14
            | exact resolve b7e14 b7e1130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1130
          have b7e1244 : (k x y) = (M.op y y) := by
            first
            | (have i₁ := b7e1243
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e1243
            | exact resolve b7e1243 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1243
          have b7e1299 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e232 x y
               have i₂ := b7e1244
               grind)
            | exact superpose b7e1244 b7e232
            | (have j0 := b7e232 x y
               grind)
            | exact resolve b7e232 b7e1244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e232 b7e1244
          have b7e1302 : (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e1299
               have r₂ := b7e22
               grind)
            | exact resolve b7e1299 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1299
          have b7e1386 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b7e33 y X0 y
               have i₂ := b7e1302
               grind)
            | exact superpose b7e1302 b7e33
            | exact resolve b7e33 b7e1302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1302
          have b7e1415 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e1386 X0
               have i₂ := b7e33 x X0 y
               grind)
            | exact superpose b7e33 b7e1386
            | exact resolve b7e1386 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e1386
          have b7e1927 : (M.op x x) ≠ (M.op x x) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e1415 x
               grind)
            | exact superpose b7e1415 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e1415 x
               grind)
            | exact resolve b7e21 b7e1415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1415
          have b7e1928 : False := by grind
          exact b7e1928
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b8e31 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b8e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b8e13 X0 X1 X2 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e31 X0 x X2 X3 x
               have i₂ := b8e13 X0 X3 x x
               grind)
            | exact superpose b8e13 b8e31
            | exact resolve b8e31 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e73 (σ X0)
               grind)
            | exact superpose b8e73 b8e19
            | exact resolve b8e19 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e90 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e73 (τ X0)
               grind)
            | exact superpose b8e73 b8e26
            | exact resolve b8e26 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e90 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e90
            | exact resolve b8e90 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e93 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e88 X0
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e88
            | exact resolve b8e88 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e95 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e91 X0
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e91
            | exact resolve b8e91 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73 b8e91
          have b8e160 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e192 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) X2) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 X1 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e34 X0 X0 x
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e34
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e34 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e206 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e160 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160
          have b8e207 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e206 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e206
          have b8e213 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) X2) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e192 X0 X1 X2
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e192 X0 (M.op X0 X0) (M.op X0 X0)
               have r₂ := b8e16 (M.op X0 X0) (M.op X0 X0)
               grind)
            | (have r₁ := b8e192 X0 X1 X2
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e192 X1 X1 X2
               have r₂ := b8e16 X1 X1
               grind)
            | exact resolve b8e192 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192
          have b8e251 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e213 X0 X1 X2
               have i₂ := b8e34 X0 X0 X2
               grind)
            | exact superpose b8e34 b8e213
            | (have j0 := b8e213 X0 X1 X2
               grind)
            | exact resolve b8e213 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e213
          have b8e329 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e207 X1 (τ X0)
               grind)
            | exact superpose b8e207 b8e26
            | (have j1 := b8e207 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e207
          have b8e3648 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e251 (σ y) X0 (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e251 X0 (σ y) (σ x)
               grind)
            | exact superpose b8e251 b8e24
            | (have j1 := b8e251 (σ y) X0 x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e251 (σ x) (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e251 (σ y) (σ x) (σ x)
               grind)
            | exact resolve b8e24 b8e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3725 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e251 X0 (σ y) (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e251 (σ y) x (σ x)
               grind)
            | exact superpose b8e251 b8e24
            | (have j1 := b8e251 X0 (σ y) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e251 (σ x) (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e251 (σ y) (σ x) (σ x)
               grind)
            | exact resolve b8e24 b8e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3733 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e95 X1
               have i₂ := b8e251 X0 (τ X1) (τ X1)
               grind)
            | (have i₁ := b8e95 X0
               have i₂ := b8e251 (τ X0) X1 (τ X0)
               grind)
            | exact superpose b8e251 b8e95
            | (have j1 := b8e251 X0 (τ X1) x
               grind)
            | exact resolve b8e95 b8e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95 b8e251
          have b8e3753 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (σ (M.op x x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e3725 X0
               have i₂ := b8e93 x
               grind)
            | exact superpose b8e93 b8e3725
            | (have j0 := b8e3725 X0
               grind)
            | exact resolve b8e3725 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3725
          have b8e3766 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e3648 X0
               have i₂ := b8e93 x
               grind)
            | exact superpose b8e93 b8e3648
            | (have j0 := b8e3648 X0
               grind)
            | exact resolve b8e3648 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3648
          have b8e7054 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e329 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e329
            | exact resolve b8e329 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e329
          have b8e7348 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e7054 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e7054
            | (have j0 := b8e7054 X0 X1
               grind)
            | exact resolve b8e7054 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7054
          have b8e142190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e3733 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e3733
            | exact resolve b8e3733 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3733
          have b8e143412 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e142190 X0 X1
               have i₂ := b8e93 X0
               grind)
            | exact superpose b8e93 b8e142190
            | (have j0 := b8e142190 X0 X1
               grind)
            | exact resolve b8e142190 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142190
          have b8e184481 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b8e3753 (σ x)
               have i₂ := b8e93 x
               grind)
            | exact superpose b8e93 b8e3753
            | (have j0 := b8e3753 (σ x)
               grind)
            | (have r₁ := b8e3753 (σ x)
               have r₂ := b8e93 x
               grind)
            | exact resolve b8e3753 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3753
          have b8e184549 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b8e184481
          have b8e184583 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e184549
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e184549
            | exact resolve b8e184549 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184549
          have b8e184621 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e184583
               grind)
            | exact superpose b8e184583 b8e24
            | exact resolve b8e24 b8e184583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184583
          have b8e184872 : (σ (M.op x x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e184621
               have i₂ := b8e93 x
               grind)
            | exact superpose b8e93 b8e184621
            | exact resolve b8e184621 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184621
          have b8e185062 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e3766 (σ x)
               have i₂ := b8e93 x
               grind)
            | exact superpose b8e93 b8e3766
            | (have j0 := b8e3766 (σ x)
               grind)
            | (have r₁ := b8e3766 (σ x)
               have r₂ := b8e93 x
               grind)
            | exact resolve b8e3766 b8e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93 b8e3766
          have b8e185131 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b8e185062
          have b8e185164 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e185131
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e185131
            | exact resolve b8e185131 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185131
          have b8e185926 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b8e184872
               have i₂ := b8e7348 y x
               grind)
            | exact superpose b8e7348 b8e184872
            | (have j1 := b8e7348 y x
               grind)
            | exact resolve b8e184872 b8e7348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7348 b8e184872
          have b8e185927 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b8e185926
               have r₂ := b8e22
               grind)
            | exact resolve b8e185926 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185926
          have b8e186405 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e185927
               have i₂ := b8e143412 x y
               grind)
            | exact superpose b8e143412 b8e185927
            | (have j1 := b8e143412 x y
               grind)
            | (have r₁ := b8e185927
               have r₂ := b8e143412 x y
               grind)
            | exact resolve b8e185927 b8e143412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143412 b8e185927
          have b8e186408 : (M.op x y) = (k y x) := by grind
          clear b8e186405
          have b8e192039 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e185164
               grind)
            | exact superpose b8e185164 b8e20
            | exact resolve b8e20 b8e185164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185164
          have b8e192376 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e192039
               have i₂ := b8e186408
               grind)
            | exact superpose b8e186408 b8e192039
            | exact resolve b8e192039 b8e186408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186408 b8e192039
          have b8e192377 : False := by grind
          exact b8e192377

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_y_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e35 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 x X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 (M.op X3 X1) X4 (M.op X0 x)
           have i₂ := b0e11 X0 X1 x X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e37 x X1 X2 X3 x
           have i₂ := b0e11 X2 X1 x x
           grind)
        | exact superpose b0e11 b0e37
        | exact resolve b0e37 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e96 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 y X2 (M.op X0 x)
           have i₂ := b0e35 X0 x
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e99 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e96 x X1 x
           have i₂ := b0e11 X1 x x x
           grind)
        | exact superpose b0e11 b0e96
        | exact resolve b0e96 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96
      have b0e127 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e39 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e39
        | exact resolve b0e39 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e328 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e127 (σ x)
           grind)
        | exact superpose b0e127 b0e18
        | exact resolve b0e18 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127
      have b0e332 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e328
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e328
        | exact resolve b0e328 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e328
      have b0e344 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e332
           have i₂ := b0e99 x
           grind)
        | exact superpose b0e99 b0e332
        | exact resolve b0e332 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99 b0e332
      have b0e349 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e344
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e344
        | exact resolve b0e344 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e344
      have b0e350 : False := by grind
      exact b0e350
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b1e12 X0 X1 x X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b1e34 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e32 x X1 X2 X3 x
             have i₂ := b1e12 X2 X1 x x
             grind)
          | exact superpose b1e12 b1e32
          | exact resolve b1e32 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 X2 X1 X3
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e12 X0 X1 X2 X3
             have i₂ := b1e17 X0 (M.op X0 X2)
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X1 X0
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e69 X0 X1 X2 x
             have i₂ := b1e34 X2 X0 x
             grind)
          | exact superpose b1e34 b1e69
          | (have j0 := b1e69 X0 X1 X2 x
             grind)
          | exact resolve b1e69 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e69
        have b1e566 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e73 X0 X1 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e567 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e566 X0 X1
             have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e566 (k X1 X1) X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e566 X1 X0
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e566 (M.op X0 X0) X1
             have r₂ := b1e17 X0 (M.op X1 X1)
             grind)
          | exact resolve b1e566 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e566
        have b1e1055 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e64 x x
             grind)
          | exact superpose b1e64 b1e21
          | (have j1 := b1e64 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e64 x y
             grind)
          | exact resolve b1e21 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e1137 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e1055
        have b1e1380 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1137
             have i₂ := b1e567 x x
             grind)
          | exact superpose b1e567 b1e1137
          | (have j1 := b1e567 (σ x) (σ x)
             grind)
          | exact resolve b1e1137 b1e567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1137
        have b1e1382 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1380
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1380
          | exact resolve b1e1380 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1380
        have b1e1383 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1382
        have b1e1387 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1383
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1383
          | exact resolve b1e1383 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1383
        have b1e1429 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e21
          | exact resolve b1e21 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1438 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e33 (σ x) (σ x)
             have i₂ := b1e1387
             grind)
          | exact superpose b1e1387 b1e33
          | exact resolve b1e33 b1e1387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e1387
        have b1e1449 : (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b1e1438
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e1438
          | exact resolve b1e1438 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1438
        have b1e1584 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1449
             have i₂ := b1e567 x x
             grind)
          | exact superpose b1e567 b1e1449
          | (have j1 := b1e567 x x
             grind)
          | exact resolve b1e1449 b1e567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e567 b1e1449
        have b1e1620 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1584
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1584
          | exact resolve b1e1584 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1584
        have b1e1624 : x = y ∨ x = (M.op x x) := by
          first
          | (have r₁ := b1e1620
             have r₂ := b1e1429
             grind)
          | exact resolve b1e1620 b1e1429
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1429 b1e1620
        have b1e1628 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1624
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1624
          | exact resolve b1e1624 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1624
        have b1e1629 : x = y := by grind
        clear b1e1628
        have b1e1760 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1629
             grind)
          | exact superpose b1e1629 b1e22
          | exact resolve b1e22 b1e1629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2133 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1760
             grind)
          | exact superpose b1e1760 b1e21
          | exact resolve b1e21 b1e1760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1760
        have b1e2161 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2133
             have i₂ := b1e1629
             grind)
          | exact superpose b1e1629 b1e2133
          | exact resolve b1e2133 b1e1629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1629 b1e2133
        have b1e2162 : False := by grind
        exact b1e2162
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e29 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e84 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 y X2 (M.op X0 x)
             have i₂ := b2e29 X0 x
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e87 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b2e84 x X1 x
             have i₂ := b2e12 X1 x x x
             grind)
          | exact superpose b2e12 b2e84
          | exact resolve b2e84 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e296 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e64 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e297 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e296
             have r₂ := b2e22
             grind)
          | exact resolve b2e296 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e296
        have b2e298 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e297
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e297
          | exact resolve b2e297 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e297
        have b2e299 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e298
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e298
          | exact resolve b2e298 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e298
        have b2e300 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e299
             grind)
          | exact superpose b2e299 b2e19
          | exact resolve b2e19 b2e299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299
        have b2e312 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e300
             have i₂ := b2e87 x
             grind)
          | exact superpose b2e87 b2e300
          | exact resolve b2e300 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87 b2e300
        have b2e314 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e312
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e312
          | exact resolve b2e312 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e312
        have b2e315 : False := by grind
        exact b2e315
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e39 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 y X0 x X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b3e12 X0 X1 x X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1
          grind
        have b3e46 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e44 x X1 X2 X3 x
             have i₂ := b3e12 X2 X1 x x
             grind)
          | exact superpose b3e12 b3e44
          | exact resolve b3e44 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e48 : y = (M.op y y) := by
          first
          | (have i₁ := b3e39 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e39
          | exact resolve b3e39 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e102 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 y X2 (M.op X0 x)
             have i₂ := b3e42 X0 x
             grind)
          | exact superpose b3e42 b3e12
          | exact resolve b3e12 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e105 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b3e102 x X1 x
             have i₂ := b3e12 X1 x x x
             grind)
          | exact superpose b3e12 b3e102
          | exact resolve b3e102 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e130 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e46 (σ x) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e46
          | exact resolve b3e46 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e323 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e130 (σ x)
             grind)
          | exact superpose b3e130 b3e19
          | exact resolve b3e19 b3e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e344 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e323
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e323
          | exact resolve b3e323 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e323
        have b3e350 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e344
             have i₂ := b3e105 x
             grind)
          | exact superpose b3e105 b3e344
          | exact resolve b3e344 b3e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105 b3e344
        have b3e942 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e72 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e72
          | exact resolve b3e72 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e1033 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e942
        have b3e1103 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1033
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e1033
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e1033 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1114 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e1103
        have b3e1125 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e1114
             have r₂ := b3e350
             grind)
          | exact resolve b3e1114 b3e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e350 b3e1114
        have b3e1258 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e45 x x
             have i₂ := b3e1125
             grind)
          | exact superpose b3e1125 b3e45
          | exact resolve b3e45 b3e1125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e1125
        have b3e1377 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1033
             have i₂ := b3e1258
             grind)
          | exact superpose b3e1258 b3e1033
          | exact resolve b3e1033 b3e1258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1033 b3e1258
        have b3e1386 : (σ x) = (σ y) := by grind
        clear b3e1377
        have b3e1456 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1386
             grind)
          | exact superpose b3e1386 b3e13
          | exact resolve b3e13 b3e1386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1485 : x = y := by
          first
          | (have i₁ := b3e1456
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1456
          | exact resolve b3e1456 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1456
        have b3e1561 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1485
             grind)
          | exact superpose b3e1485 b3e19
          | exact resolve b3e19 b3e1485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1569 : x = (M.op x x) := by
          first
          | (have i₁ := b3e48
             have i₂ := b3e1485
             grind)
          | exact superpose b3e1485 b3e48
          | exact resolve b3e48 b3e1485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e1485
        have b3e1571 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1561
             have i₂ := b3e1569
             grind)
          | exact superpose b3e1569 b3e1561
          | exact resolve b3e1561 b3e1569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1561 b3e1569
        have b3e1572 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1571
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1571
          | exact resolve b3e1571 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1571
        have b3e1573 : False := by grind
        exact b3e1573
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b4e28 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
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
          have b4e31 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ x) X1 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b4e13 X0 X1 x X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b4e35 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e33 x X1 X2 X3 x
               have i₂ := b4e13 X2 X1 x x
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e37 : y = (M.op y y) := by
            first
            | (have i₁ := b4e28 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e28
            | exact resolve b4e28 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e66 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X1 X3
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2 X3
               have i₂ := b4e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e66 X0 X1 X2 x
               have i₂ := b4e35 X2 X0 x
               grind)
            | exact superpose b4e35 b4e66
            | (have j0 := b4e66 X0 X1 X2 x
               grind)
            | exact resolve b4e66 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e86 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 x) ∨ (M.op X0 X1) = (M.op y y) ∨ (M.op X0 X1) = (k y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 y (M.op X0 X1)
               have i₂ := b4e31 X0 X1
               grind)
            | exact superpose b4e31 b4e17
            | (have j0 := b4e17 y (M.op X0 X1)
               grind)
            | (have r₁ := b4e17 y (M.op X0 x)
               have r₂ := b4e31 X0 x
               grind)
            | exact resolve b4e17 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e88 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 y X2 (M.op X0 x)
               have i₂ := b4e31 X0 x
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e91 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b4e88 x X1 x
               have i₂ := b4e13 X1 x x x
               grind)
            | exact superpose b4e13 b4e88
            | exact resolve b4e88 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88
          have b4e93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 x) ∨ (M.op X0 X1) = y ∨ (M.op X0 X1) = (k y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e86 X0 X1
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e86
            | (have j0 := b4e86 X0 X1
               grind)
            | exact resolve b4e86 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e86
          have b4e105 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e35 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e227 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e105 (σ x)
               grind)
            | exact superpose b4e105 b4e20
            | exact resolve b4e20 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e245 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e227
               have i₂ := b4e91 x
               grind)
            | exact superpose b4e91 b4e227
            | exact resolve b4e227 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e227
          have b4e313 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (M.op (σ y) (σ y)) ∨ (M.op X0 X1) = (k (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ y) (M.op X0 X1)
               have i₂ := b4e32 X0 X1
               grind)
            | exact superpose b4e32 b4e17
            | (have j0 := b4e17 (σ y) (M.op X0 X1)
               grind)
            | (have r₁ := b4e17 (σ y) (M.op X0 (σ x))
               have r₂ := b4e32 X0 (σ x)
               grind)
            | exact resolve b4e17 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e325 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (σ x)) ∨ (M.op X0 X1) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (k (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e313 X0 X1
               have i₂ := b4e105 (σ y)
               grind)
            | exact superpose b4e105 b4e313
            | (have j0 := b4e313 X0 X1
               grind)
            | (have r₁ := b4e313 X0 (σ y)
               have r₂ := b4e105 X0
               grind)
            | exact resolve b4e313 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e313
          have b4e334 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (σ y) ∨ (M.op X0 X1) = (k (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e325 X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e325
            | (have j0 := b4e325 X0 X1
               grind)
            | exact resolve b4e325 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e325
          have b4e457 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e70 (σ x) X0 (σ x)
               grind)
            | (have i₁ := b4e23
               have i₂ := b4e70 X0 (σ x) (σ x)
               grind)
            | exact superpose b4e70 b4e23
            | (have j1 := b4e70 (σ x) X0 x
               grind)
            | exact resolve b4e23 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e485 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e70 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e486 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e485 X0 X1
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e485 (k X1 X1) X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e485 X1 X0
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e485 (M.op X0 X0) X1
               have r₂ := b4e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b4e485 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e485
          have b4e993 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (σ X1) (σ X0)
               have i₂ := b4e60 X0 X1
               grind)
            | exact superpose b4e60 b4e34
            | (have j1 := b4e60 X1 X0
               grind)
            | exact resolve b4e34 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1003 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e1004 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e1003 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1003
          have b4e1017 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e993 X0 X1
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e993
            | (have j0 := b4e993 X0 X1
               grind)
            | exact resolve b4e993 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e993
          have b4e3536 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e457 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e457
            | (have j0 := b4e457 (σ y)
               grind)
            | (have r₁ := b4e457 (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e457 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e457
          have b4e3537 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e3536
          have b4e3539 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3537
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e3537
            | exact resolve b4e3537 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3537
          have b4e3542 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e3539
               have i₂ := b4e105 (σ x)
               grind)
            | exact superpose b4e105 b4e3539
            | exact resolve b4e3539 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105 b4e3539
          have b4e3560 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b4e34 (σ x) (σ x)
               have i₂ := b4e3542
               grind)
            | exact superpose b4e3542 b4e34
            | exact resolve b4e34 b4e3542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3542
          have b4e3582 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e3560
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e3560
            | exact resolve b4e3560 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3560
          have b4e5315 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e3582
               grind)
            | exact superpose b4e3582 b4e14
            | exact resolve b4e14 b4e3582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3582
          have b4e5368 : (σ x) = (σ (k x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e5315
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e5315
            | exact resolve b4e5315 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5315
          have b4e5650 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (σ X1) (σ X1)
               have i₂ := b4e1017 X0 X1
               grind)
            | exact superpose b4e1017 b4e34
            | (have j1 := b4e1017 X0 X1
               grind)
            | exact resolve b4e34 b4e1017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e1017
          have b4e5696 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e5650 X0 X1
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e5650
            | (have j0 := b4e5650 X0 X1
               grind)
            | exact resolve b4e5650 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5650
          have b4e5697 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e5696 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5696
          have b4e5838 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e1004 x
               have i₂ := b4e5368
               grind)
            | exact superpose b4e5368 b4e1004
            | (have j0 := b4e1004 x
               grind)
            | (have r₁ := b4e1004 x
               have r₂ := b4e5368
               grind)
            | exact resolve b4e1004 b4e5368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1004 b4e5368
          have b4e5869 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by grind
          clear b4e5838
          have b4e6269 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e245
               have i₂ := b4e5869
               grind)
            | exact superpose b4e5869 b4e245
            | exact resolve b4e245 b4e5869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6270 : (σ x) ≠ (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e5869
               grind)
            | exact superpose b4e5869 b4e23
            | exact resolve b4e23 b4e5869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6294 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e334 (σ x) (σ x)
               have i₂ := b4e5869
               grind)
            | exact superpose b4e5869 b4e334
            | exact resolve b4e334 b4e5869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e334 b4e5869
          have b4e6302 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
          clear b4e6294
          have b4e6311 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e6302
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e6302
            | exact resolve b4e6302 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6302
          have b4e6316 : (σ x) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b4e6311
               have r₂ := b4e6270
               grind)
            | exact resolve b4e6311 b4e6270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6270 b4e6311
          have b4e6930 : (k y x) = (τ (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e6316
               grind)
            | exact superpose b4e6316 b4e14
            | exact resolve b4e14 b4e6316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6316
          have b4e6985 : y = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e6930
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e6930
            | exact resolve b4e6930 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6930
          have b4e7435 : x ≠ y ∨ x = (k y x) := by grind
          clear b4e6985
          have b4e20133 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e5697 (τ X0) X1
               grind)
            | exact superpose b4e5697 b4e26
            | (have j1 := b4e5697 (τ X0) X1
               grind)
            | exact resolve b4e26 b4e5697
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e20135 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 X0)
               have i₂ := b4e5697 X0 X1
               grind)
            | exact superpose b4e5697 b4e14
            | (have j1 := b4e5697 X0 X1
               grind)
            | exact resolve b4e14 b4e5697
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5697
          have b4e20364 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e20135 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e20135
            | (have j0 := b4e20135 X0 X1
               grind)
            | exact resolve b4e20135 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20135
          have b4e20366 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e20133 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e20133
            | (have j0 := b4e20133 X0 X1
               grind)
            | exact resolve b4e20133 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20133
          have b4e20415 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e20366 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e20366
            | (have j0 := b4e20366 X0 X1
               grind)
            | exact resolve b4e20366 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20366
          have b4e20425 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e20415 X0 X1
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e20415
            | (have j0 := b4e20415 X0 X1
               grind)
            | exact resolve b4e20415 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e20415
          have b4e20760 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e20425 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e20425
            | (have j0 := b4e20425 X1 X1
               grind)
            | exact resolve b4e20425 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20425
          have b4e21727 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 X0 X0
               have i₂ := b4e20760 X1 X0
               grind)
            | exact superpose b4e20760 b4e486
            | (have j0 := b4e486 X0 X1
               have j1 := b4e20760 X1 X0
               grind)
            | exact resolve b4e486 b4e20760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e486 b4e20760
          have b4e21774 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e21727 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21727
          have b4e29333 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e245
               have i₂ := b4e20364 x x
               grind)
            | exact superpose b4e20364 b4e245
            | (have j1 := b4e20364 x x
               grind)
            | exact resolve b4e245 b4e20364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e245 b4e20364
          have b4e31681 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e29333
               have i₂ := b4e21774 x x
               grind)
            | exact superpose b4e21774 b4e29333
            | (have j1 := b4e21774 x x
               grind)
            | exact resolve b4e29333 b4e21774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21774 b4e29333
          have b4e31692 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e31681
          have b4e31693 : x = (M.op x x) := by grind
          clear b4e31692
          have b4e32841 : (σ x) ≠ (σ x) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e6269
               have i₂ := b4e31693
               grind)
            | exact superpose b4e31693 b4e6269
            | exact resolve b4e6269 b4e31693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6269
          have b4e32843 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e31693
               grind)
            | exact superpose b4e31693 b4e21
            | exact resolve b4e21 b4e31693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32860 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e93 x x
               have i₂ := b4e31693
               grind)
            | exact superpose b4e31693 b4e93
            | exact resolve b4e93 b4e31693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93 b4e31693
          have b4e32877 : x = y ∨ x = (k y x) := by grind
          clear b4e32860
          have b4e32881 : y = (k y x) := by grind
          clear b4e32841
          have b4e32882 : x = (k y x) := by
            first
            | (have r₁ := b4e32877
               have r₂ := b4e7435
               grind)
            | exact resolve b4e32877 b4e7435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7435 b4e32877
          have b4e33623 : x = y := by
            first
            | (have i₁ := b4e32881
               have i₂ := b4e32882
               grind)
            | exact superpose b4e32882 b4e32881
            | exact resolve b4e32881 b4e32882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32881 b4e32882
          have b4e33668 : False := by grind
          exact b4e33668
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b5e28 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 x X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b5e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b5e13 X0 X1 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 x X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b5e13 X0 X1 x X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b5e33 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e31 x X1 X2 X3 x
               have i₂ := b5e13 X2 X1 x x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e34 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e29 X0 x X2 X3 x
               have i₂ := b5e13 X0 X3 x x
               grind)
            | exact superpose b5e13 b5e29
            | exact resolve b5e29 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e42 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e45 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e42
          have b5e48 : y = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X1 X3
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e63 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e59 X0 X1 X2 x
               have i₂ := b5e33 X2 X0 x
               grind)
            | exact superpose b5e33 b5e59
            | (have j0 := b5e59 X0 X1 X2 x
               grind)
            | exact resolve b5e59 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e80 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 y X2 (M.op X0 x)
               have i₂ := b5e30 X0 x
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e83 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b5e80 x X1 x
               have i₂ := b5e13 X1 x x x
               grind)
            | exact superpose b5e13 b5e80
            | exact resolve b5e80 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80
          have b5e155 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X1 X1) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X1 (M.op X0 X2)
               have i₂ := b5e34 X0 X2 X1
               grind)
            | exact superpose b5e34 b5e17
            | (have j0 := b5e17 X1 (M.op X0 X2)
               grind)
            | (have r₁ := b5e17 x (M.op X0 x)
               have r₂ := b5e34 X0 x x
               grind)
            | exact resolve b5e17 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e184 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b5e191 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e259 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e260 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e259
               have r₂ := b5e24
               grind)
            | exact resolve b5e259 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259
          have b5e261 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e260
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e260
            | exact resolve b5e260 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e260
          have b5e262 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e261
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e261
            | exact resolve b5e261 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e261
          have b5e263 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e262
               grind)
            | exact superpose b5e262 b5e20
            | exact resolve b5e20 b5e262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e269 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e34 (σ x) (σ y) X0
               have i₂ := b5e262
               grind)
            | exact superpose b5e262 b5e34
            | exact resolve b5e34 b5e262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e274 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e263
               have i₂ := b5e83 x
               grind)
            | exact superpose b5e83 b5e263
            | exact resolve b5e263 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e263
          have b5e340 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e63 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e341 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e340 X0 X1
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e340 (k X1 X1) X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e340 X1 X0
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e340 (M.op X0 X0) X1
               have r₂ := b5e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b5e340 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e340
          have b5e530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e341 (σ X1) (σ X0)
               grind)
            | exact superpose b5e341 b5e19
            | (have j1 := b5e341 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e532 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e26 X0 X1
               have i₂ := b5e341 X1 (τ X0)
               grind)
            | exact superpose b5e341 b5e26
            | (have j1 := b5e341 X1 (τ X0)
               grind)
            | exact resolve b5e26 b5e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e701 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e53 X1 X0
               grind)
            | exact superpose b5e53 b5e17
            | (have j0 := b5e17 (σ X1) (σ X0)
               have j1 := b5e53 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e53 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e53 X0 X1
               grind)
            | exact resolve b5e17 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e704 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 (σ X1) (σ X0)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e32
            | (have j1 := b5e53 X1 X0
               grind)
            | exact resolve b5e32 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e714 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e53 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e715 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e714 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e714
          have b5e717 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e701 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e701
          have b5e718 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e717 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e717
          have b5e728 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e704 X0 X1
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e704
            | (have j0 := b5e704 X0 X1
               grind)
            | exact resolve b5e704 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e704
          have b5e729 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e718 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e718
            | (have j0 := b5e718 X0 X1
               grind)
            | exact resolve b5e718 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e718
          have b5e1072 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e715 (τ X0)
               have i₂ := b5e27 X0 (τ X0)
               grind)
            | exact superpose b5e27 b5e715
            | (have j0 := b5e715 (τ X0)
               grind)
            | exact resolve b5e715 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e715
          have b5e1077 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1072 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1072
            | (have j0 := b5e1072 X0
               grind)
            | exact resolve b5e1072 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1072
          have b5e1081 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1077 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e1077
            | (have j0 := b5e1077 X0
               grind)
            | exact resolve b5e1077 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1077
          have b5e2776 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e155 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e155
          have b5e3316 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e532 (σ X0) X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e532
            | exact resolve b5e532 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e532
          have b5e3378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e3316 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e3316
            | (have j0 := b5e3316 X0 X1
               grind)
            | exact resolve b5e3316 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3316
          have b5e6215 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32 (σ X1) (σ X1)
               have i₂ := b5e728 X0 X1
               grind)
            | exact superpose b5e728 b5e32
            | (have j1 := b5e728 X0 X1
               grind)
            | exact resolve b5e32 b5e728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e728
          have b5e6259 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e6215 X0 X1
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e6215
            | (have j0 := b5e6215 X0 X1
               grind)
            | exact resolve b5e6215 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6215
          have b5e6260 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e6259 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6259
          have b5e6547 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e729 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e729
            | exact resolve b5e729 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6731 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e729
          have b5e6789 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e6731 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e6731
            | (have j0 := b5e6731 X0 X1
               grind)
            | exact resolve b5e6731 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6731
          have b5e6790 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e6789 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6789
          have b5e6840 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e6547 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e6547
            | (have j0 := b5e6547 X0 X1
               grind)
            | exact resolve b5e6547 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6547
          have b5e6862 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e6840 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e6840
            | (have j0 := b5e6840 X0 X1
               grind)
            | exact resolve b5e6840 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6840
          have b5e16784 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e26 X0 (τ X0)
               have i₂ := b5e6260 (τ X0) X1
               grind)
            | exact superpose b5e6260 b5e26
            | (have j1 := b5e6260 (τ X0) X1
               grind)
            | exact resolve b5e26 b5e6260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e16786 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 X0)
               have i₂ := b5e6260 X0 X1
               grind)
            | exact superpose b5e6260 b5e14
            | (have j1 := b5e6260 X0 X1
               grind)
            | exact resolve b5e14 b5e6260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16871 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e6260 x y
               grind)
            | exact superpose b5e6260 b5e24
            | (have j1 := b5e6260 x x
               grind)
            | exact resolve b5e24 b5e6260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6260
          have b5e16991 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16786 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e16786
            | (have j0 := b5e16786 X0 X1
               grind)
            | exact resolve b5e16786 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16786
          have b5e16993 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e16784 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e16784
            | (have j0 := b5e16784 X0 X1
               grind)
            | exact resolve b5e16784 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16784
          have b5e17035 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e16993 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e16993
            | (have j0 := b5e16993 X0 X1
               grind)
            | exact resolve b5e16993 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16993
          have b5e17045 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e17035 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e17035
            | (have j0 := b5e17035 X0 X1
               grind)
            | exact resolve b5e17035 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17035
          have b5e19018 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e16871
               have i₂ := b5e3378 y x
               grind)
            | exact superpose b5e3378 b5e16871
            | (have j1 := b5e3378 y x
               grind)
            | exact resolve b5e16871 b5e3378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16871
          have b5e19019 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e19018
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e19018
            | exact resolve b5e19018 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19018
          have b5e19020 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by grind
          clear b5e19019
          have b5e19035 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e19020
               have i₂ := b5e83 x
               grind)
            | exact superpose b5e83 b5e19020
            | exact resolve b5e19020 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19020
          have b5e19239 : (k x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e19035
               grind)
            | exact superpose b5e19035 b5e14
            | exact resolve b5e14 b5e19035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19035
          have b5e19342 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e19239
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e19239
            | exact resolve b5e19239 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19239
          have b5e19343 : x = (M.op x x) := by
            first
            | (have j1 := b5e1081 x
               grind)
            | (have r₁ := b5e19342
               have r₂ := b5e1081 x
               grind)
            | exact resolve b5e19342 b5e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19342
          have b5e20151 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e19343
               grind)
            | exact superpose b5e19343 b5e21
            | exact resolve b5e21 b5e19343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19343
          have b5e22789 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e6790 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6790
            | exact resolve b5e6790 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6790
          have b5e22998 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e22789 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e22789
            | (have j0 := b5e22789 X0 X1
               grind)
            | exact resolve b5e22789 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22789
          have b5e23024 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e22998 X0 X1
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e22998
            | (have j0 := b5e22998 X0 X1
               grind)
            | exact resolve b5e22998 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e22998
          have b5e26745 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17045 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e17045
            | (have j0 := b5e17045 X1 X1
               grind)
            | exact resolve b5e17045 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17045
          have b5e27664 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e341 X0 X0
               have i₂ := b5e26745 X1 X0
               grind)
            | exact superpose b5e26745 b5e341
            | (have j0 := b5e341 X0 X1
               have j1 := b5e26745 X1 X0
               grind)
            | exact resolve b5e341 b5e26745
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27719 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e27664 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27664
          have b5e40030 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e23024 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e23024
            | exact resolve b5e23024 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23024
          have b5e40459 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e40030 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40602 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X0 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40459 X0 (M.op X2 X1)
               have i₂ := b5e33 X1 X0 X2
               grind)
            | exact superpose b5e33 b5e40459
            | (have j0 := b5e40459 X0 (M.op X2 X1)
               grind)
            | (have r₁ := b5e40459 X2 (M.op X2 X1)
               have r₂ := b5e33 X1 X2 X2
               grind)
            | exact resolve b5e40459 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40614 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X2) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40459 (M.op X0 X2) X1
               have i₂ := b5e34 X0 X2 X1
               grind)
            | exact superpose b5e34 b5e40459
            | (have j0 := b5e40459 X0 X1
               grind)
            | exact resolve b5e40459 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42651 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e40614 (σ x) (σ y) X0
               have i₂ := b5e262
               grind)
            | exact superpose b5e262 b5e40614
            | (have j0 := b5e40614 (σ x) (σ y) X0
               grind)
            | (have r₁ := b5e40614 (σ x) (σ y) x
               have r₂ := b5e262
               grind)
            | exact resolve b5e40614 b5e262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42683 : ∀ X0 : G, (σ y) = (k (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e42651 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42651
          have b5e46468 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op (σ x) X0)) y) := by
            intro X0
            first
            | (have i₁ := b5e184 (M.op (σ x) X0) y
               have i₂ := b5e42683 X0
               grind)
            | exact superpose b5e42683 b5e184
            | exact resolve b5e184 b5e42683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42683
          have b5e46529 : ∀ X0 : G, y = (k (τ (M.op (σ x) X0)) y) := by
            intro X0
            first
            | (have i₁ := b5e46468 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e46468
            | exact resolve b5e46468 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46468
          have b5e46660 : ∀ X0 : G, y = (k (τ (σ (k x X0))) y) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e46529 (σ X0)
               have i₂ := b5e16991 X0 x
               grind)
            | exact superpose b5e16991 b5e46529
            | (have j1 := b5e16991 X0 x
               grind)
            | exact resolve b5e46529 b5e16991
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46812 : ∀ X0 : G, y = (k (k x X0) y) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e46660 X0
               have i₂ := b5e14 (k x X0)
               grind)
            | exact superpose b5e14 b5e46660
            | (have j0 := b5e46660 X0
               grind)
            | exact resolve b5e46660 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46660
          have b5e47874 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2776 X1 (σ X0)
               have i₂ := b5e6862 (M.op X1 (σ X0)) X0
               grind)
            | exact superpose b5e6862 b5e2776
            | (have j0 := b5e2776 X1 (σ X0)
               have j1 := b5e6862 (M.op X1 (σ X0)) X0
               grind)
            | exact resolve b5e2776 b5e6862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2776 b5e6862
          have b5e48058 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have j0 := b5e47874 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47874
          have b5e48076 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have j0 := b5e48058 X0 X1
               have j1 := b5e40602 (σ X0) (σ X0) X1
               grind)
            | (have r₁ := b5e48058 X0 x
               have r₂ := b5e40602 (σ X0) (σ X0) x
               grind)
            | (have r₁ := b5e48058 X0 X0
               have r₂ := b5e40602 X0 (σ X0) (σ X0)
               grind)
            | exact resolve b5e48058 b5e40602
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40602 b5e48058
          have b5e48096 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k (σ X0) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have j0 := b5e48076 X0 X1
               have j1 := b5e40459 (σ X0) (M.op X1 (σ X0))
               grind)
            | (have r₁ := b5e48076 X0 X1
               have r₂ := b5e40459 (σ X0) (M.op X1 (σ X0))
               grind)
            | exact resolve b5e48076 b5e40459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48076
          have b5e48134 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e48096 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e48096
            | exact resolve b5e48096 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48286 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e191 X1 (M.op X0 (σ X1))
               have i₂ := b5e48096 X1 X0
               grind)
            | exact superpose b5e48096 b5e191
            | exact resolve b5e191 b5e48096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48096
          have b5e49223 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (k (M.op X3 X1) (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e48134 (M.op X3 X1) (M.op X0 x)
               have i₂ := b5e13 X0 X1 x X3
               grind)
            | exact superpose b5e13 b5e48134
            | exact resolve b5e48134 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e59859 : ∀ X0 : G, y = (k (M.op x X0) y) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e46812 X0
               have i₂ := b5e26745 x X0
               grind)
            | exact superpose b5e26745 b5e46812
            | (have j0 := b5e46812 X0
               have j1 := b5e26745 X0 X0
               grind)
            | exact resolve b5e46812 b5e26745
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46812
          have b5e60138 : ∀ X0 : G, y = (k (M.op x X0) y) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e59859 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59859
          have b5e64711 : ∀ X0 : G, (σ y) = (σ (M.op (M.op x X0) y)) ∨ y = (M.op y (M.op x X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e3378 (M.op x X0) y
               have i₂ := b5e60138 X0
               grind)
            | exact superpose b5e60138 b5e3378
            | (have j0 := b5e3378 (M.op x X0) y
               have j1 := b5e60138 X0
               grind)
            | exact resolve b5e3378 b5e60138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3378 b5e60138
          have b5e64930 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ y = (M.op y (M.op x X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e64711 X0
               have i₂ := b5e30 x X0
               grind)
            | exact superpose b5e30 b5e64711
            | (have j0 := b5e64711 X0
               grind)
            | exact resolve b5e64711 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64711
          have b5e65007 : ∀ X0 : G, y = (M.op y (M.op x X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e64930 X0
               grind)
            | (have r₁ := b5e64930 X0
               have r₂ := b5e274
               grind)
            | exact resolve b5e64930 b5e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64930
          have b5e65063 : ∀ X0 : G, (k X0 X0) = X0 ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e65007 X0
               have i₂ := b5e28 X0 x
               grind)
            | exact superpose b5e28 b5e65007
            | (have j0 := b5e65007 X0
               grind)
            | exact resolve b5e65007 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65007
          have b5e66136 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e27719 X0 X0
               have i₂ := b5e65063 X0
               grind)
            | exact superpose b5e65063 b5e27719
            | (have j0 := b5e27719 X0 x
               have j1 := b5e65063 X0
               grind)
            | exact resolve b5e27719 b5e65063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66178 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ y = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e191 X0 (σ X0)
               have i₂ := b5e65063 (σ X0)
               grind)
            | exact superpose b5e65063 b5e191
            | (have j1 := b5e65063 (σ X0)
               grind)
            | exact resolve b5e191 b5e65063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e191 b5e65063
          have b5e66224 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b5e66136 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66136
          have b5e66302 : ∀ X0 : G, (k X0 X0) = X0 ∨ y = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e66178 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e66178
            | (have j0 := b5e66178 X0
               grind)
            | exact resolve b5e66178 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66178
          have b5e67652 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 X0 y
               have i₂ := b5e66224 X1
               grind)
            | exact superpose b5e66224 b5e33
            | (have j1 := b5e66224 X1
               grind)
            | exact resolve b5e33 b5e66224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e67766 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e67652 X0 X1
               have i₂ := b5e83 X0
               grind)
            | exact superpose b5e83 b5e67652
            | (have j0 := b5e67652 X0 X1
               grind)
            | exact resolve b5e67652 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67652
          have b5e71687 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (σ X1)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e33 (σ X1) X0 y
               have i₂ := b5e66302 X1
               grind)
            | exact superpose b5e66302 b5e33
            | (have j1 := b5e66302 X1
               grind)
            | exact resolve b5e33 b5e66302
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66302
          have b5e71801 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (σ X1)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e71687 X0 X1
               have i₂ := b5e83 X0
               grind)
            | exact superpose b5e83 b5e71687
            | (have j0 := b5e71687 X0 X1
               grind)
            | exact resolve b5e71687 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71687
          have b5e86994 : ∀ X0 : G, (σ y) ≠ (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e274
               have i₂ := b5e67766 x X0
               grind)
            | (have i₁ := b5e274
               have i₂ := b5e67766 x x
               grind)
            | exact superpose b5e67766 b5e274
            | (have j1 := b5e67766 X0 X0
               grind)
            | exact resolve b5e274 b5e67766
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e274 b5e67766
          have b5e202180 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e48286 (σ X1) X0
               have i₂ := b5e530 X0 X1
               grind)
            | exact superpose b5e530 b5e48286
            | (have j1 := b5e530 X1 X0
               grind)
            | exact resolve b5e48286 b5e530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48286
          have b5e202585 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e202180 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e202180
            | (have j0 := b5e202180 X0 X1
               grind)
            | exact resolve b5e202180 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e202180
          have b5e317561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) x) ∨ (k X1 X1) = X1 ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e16991 X1 X0
               have i₂ := b5e71801 (σ X0) X1
               grind)
            | exact superpose b5e71801 b5e16991
            | (have j0 := b5e16991 X1 X1
               have j1 := b5e71801 X0 X1
               grind)
            | exact resolve b5e16991 b5e71801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16991 b5e71801
          have b5e318103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) x) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e317561 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e317561
          have b5e1088562 : ∀ X0 X1 : G, (M.op (σ X0) x) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e318103 X0 X1
               have i₂ := b5e26745 X0 X1
               grind)
            | exact superpose b5e26745 b5e318103
            | (have j0 := b5e318103 X0 X1
               have j1 := b5e26745 X0 X1
               grind)
            | exact resolve b5e318103 b5e26745
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26745 b5e318103
          have b5e1089058 : ∀ X0 X1 : G, (M.op (σ X0) x) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e1088562 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1088562
          have b5e1303940 : ∀ X0 : G, (σ y) = (M.op (σ y) x) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1089058 y X0
               have i₂ := b5e66224 X0
               grind)
            | exact superpose b5e66224 b5e1089058
            | (have j0 := b5e1089058 X0 X0
               have j1 := b5e66224 X0
               grind)
            | exact resolve b5e1089058 b5e66224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66224
          have b5e1303991 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) x) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e86994 X0
               have i₂ := b5e1089058 x X0
               grind)
            | exact superpose b5e1089058 b5e86994
            | (have j0 := b5e86994 X0
               have j1 := b5e1089058 X0 X0
               grind)
            | exact resolve b5e86994 b5e1089058
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86994 b5e1089058
          have b5e1304054 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) x) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e1303991 X0
               have j1 := b5e1081 X0
               grind)
            | (have r₁ := b5e1303991 X0
               have r₂ := b5e1081 X0
               grind)
            | exact resolve b5e1303991 b5e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1081 b5e1303991
          have b5e1304062 : ∀ X0 : G, (σ y) = (M.op (σ y) x) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e1303940 X0
               have j1 := b5e40459 X0 X0
               grind)
            | (have r₁ := b5e1303940 x
               have r₂ := b5e40459 x x
               grind)
            | exact resolve b5e1303940 b5e40459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1303940
          have b5e1304082 : ∀ X0 : G, (σ y) = (M.op (σ x) x) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1304062 X0
               have i₂ := b5e269 x
               grind)
            | exact superpose b5e269 b5e1304062
            | (have j0 := b5e1304062 X0
               grind)
            | exact resolve b5e1304062 b5e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e269 b5e1304062
          have b5e1319020 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ y) = (M.op (σ x) x) := by
            intro X0
            first
            | (have i₁ := b5e27719 X0 X0
               have i₂ := b5e1304082 X0
               grind)
            | exact superpose b5e1304082 b5e27719
            | (have j0 := b5e27719 X0 x
               grind)
            | exact resolve b5e27719 b5e1304082
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27719 b5e1304082
          have b5e1319062 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ y) = (M.op (σ x) x) := by
            intro X0
            first
            | (have j0 := b5e1319020 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1319020
          have b5e1319095 : ∀ X0 : G, (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e1319062 X0
               have j1 := b5e1304054 X0
               grind)
            | (have r₁ := b5e1319062 X0
               have r₂ := b5e1304054 X0
               grind)
            | exact resolve b5e1319062 b5e1304054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1304054 b5e1319062
          have b5e1320584 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e40614 X0 X0 X1
               have i₂ := b5e1319095 X0
               grind)
            | exact superpose b5e1319095 b5e40614
            | (have j0 := b5e40614 X0 X0 X1
               grind)
            | (have r₁ := b5e40614 X0 X0 x
               have r₂ := b5e1319095 X0
               grind)
            | exact resolve b5e40614 b5e1319095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40614
          have b5e1320587 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e49223 X0 X0 x
               have i₂ := b5e1319095 X0
               grind)
            | exact superpose b5e1319095 b5e49223
            | exact resolve b5e49223 b5e1319095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49223
          have b5e1320782 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e1320584 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1320584
          have b5e1337869 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e184 (M.op X1 (σ X0)) X0
               have i₂ := b5e1320587 (σ X0) X1
               grind)
            | exact superpose b5e1320587 b5e184
            | exact resolve b5e184 b5e1320587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1320587
          have b5e1337929 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1337869 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1337869
            | exact resolve b5e1337869 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1337869
          have b5e1340426 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e184 (M.op (σ X0) X1) X0
               have i₂ := b5e1320782 (σ X0) X1
               grind)
            | exact superpose b5e1320782 b5e184
            | exact resolve b5e184 b5e1320782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184 b5e1320782
          have b5e1340487 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1340426 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1340426
            | exact resolve b5e1340426 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1340426
          have b5e1342223 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1337929 X1 (σ X0)
               have i₂ := b5e530 X1 X0
               grind)
            | exact superpose b5e530 b5e1337929
            | (have j1 := b5e530 X1 X0
               grind)
            | exact resolve b5e1337929 b5e530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e530 b5e1337929
          have b5e1342386 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e1342223 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1342223
            | (have j0 := b5e1342223 X0 X1
               grind)
            | exact resolve b5e1342223 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1342223
          have b5e4406430 : ∀ X0 : G, y = (k (τ (σ (k x X0))) y) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e46529 (σ X0)
               have i₂ := b5e202585 X0 x
               grind)
            | exact superpose b5e202585 b5e46529
            | (have j1 := b5e202585 y (τ (σ (k x X0)))
               grind)
            | exact resolve b5e46529 b5e202585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46529 b5e202585
          have b5e4406507 : ∀ X0 : G, y = (k (k x X0) y) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4406430 X0
               have i₂ := b5e14 (k x X0)
               grind)
            | exact superpose b5e14 b5e4406430
            | (have j0 := b5e4406430 X0
               grind)
            | exact resolve b5e4406430 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4406430
          have b5e4409399 : ∀ X0 : G, y = (k (M.op x X0) y) ∨ (M.op x X0) = X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4406507 x
               have i₂ := b5e40030 x x
               grind)
            | exact superpose b5e40030 b5e4406507
            | (have j0 := b5e4406507 X0
               have j1 := b5e40030 (M.op x X0) y
               grind)
            | exact resolve b5e4406507 b5e40030
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40030 b5e4406507
          have b5e4409482 : ∀ X0 : G, y = (k (M.op x X0) y) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e4409399 X0
               have j1 := b5e40459 (M.op x X0) y
               grind)
            | (have r₁ := b5e4409399 x
               have r₂ := b5e40459 x x
               grind)
            | exact resolve b5e4409399 b5e40459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4409399
          have b5e4420612 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op y (M.op x X0)) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e341 y (M.op x X0)
               have i₂ := b5e4409482 X0
               grind)
            | exact superpose b5e4409482 b5e341
            | (have j0 := b5e341 y (M.op x X0)
               have j1 := b5e4409482 X0
               grind)
            | exact resolve b5e341 b5e4409482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4409482
          have b5e4420663 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op y (M.op x X0)) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4420612 X0
               have i₂ := b5e30 x X0
               grind)
            | exact superpose b5e30 b5e4420612
            | (have j0 := b5e4420612 X0
               grind)
            | exact resolve b5e4420612 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e4420612
          have b5e4420672 : ∀ X0 : G, y = (M.op y (M.op x X0)) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e4420663 X0
               grind)
            | (have r₁ := b5e4420663 X0
               have r₂ := b5e21
               grind)
            | exact resolve b5e4420663 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4420663
          have b5e4420678 : ∀ X0 : G, (k x X0) = X0 ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e4420672 X0
               have i₂ := b5e28 X0 x
               grind)
            | exact superpose b5e28 b5e4420672
            | (have j0 := b5e4420672 X0
               grind)
            | exact resolve b5e4420672 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e4420672
          have b5e4423668 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op X0 x) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e341 X0 x
               have i₂ := b5e4420678 X0
               grind)
            | exact superpose b5e4420678 b5e341
            | (have j0 := b5e341 y X0
               have j1 := b5e4420678 X0
               grind)
            | exact resolve b5e341 b5e4420678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4420678
          have b5e7139467 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 x) ∨ y = (M.op y X0) ∨ (M.op x X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e33 x X1 X0
               have i₂ := b5e4423668 X0
               grind)
            | exact superpose b5e4423668 b5e33
            | (have j1 := b5e4423668 X0
               grind)
            | exact resolve b5e33 b5e4423668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4423668
          have b5e10640357 : ∀ X0 X1 : G, (k (τ (σ (k X0 X1))) X0) = X0 ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1340487 X0 (σ X1)
               have i₂ := b5e1342386 X1 X0
               grind)
            | exact superpose b5e1342386 b5e1340487
            | (have j1 := b5e1342386 (τ (σ (k X0 X1))) X0
               grind)
            | exact resolve b5e1340487 b5e1342386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1340487 b5e1342386
          have b5e10640371 : ∀ X0 X1 : G, (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e10640357 X0 X1
               have i₂ := b5e14 (k X0 X1)
               grind)
            | exact superpose b5e14 b5e10640357
            | (have j0 := b5e10640357 X0 (k X0 X1)
               grind)
            | exact resolve b5e10640357 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10640357
          have b5e16567454 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e7139467 X0 y
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e7139467 x y
               grind)
            | exact superpose b5e7139467 b5e22
            | (have j1 := b5e7139467 X0 x
               grind)
            | exact resolve b5e22 b5e7139467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7139467
          have b5e16567468 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e16567454 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16567454
          have b5e16567497 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op x X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 X0 y
               have i₂ := b5e16567468 X1
               grind)
            | exact superpose b5e16567468 b5e33
            | (have j1 := b5e16567468 X1
               grind)
            | exact resolve b5e33 b5e16567468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16567468
          have b5e16567794 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) ∨ (M.op x X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e16567497 X0 X1
               have i₂ := b5e83 X0
               grind)
            | exact superpose b5e83 b5e16567497
            | (have j0 := b5e16567497 X0 X1
               grind)
            | exact resolve b5e16567497 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83 b5e16567497
          have b5e16797723 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1319095 X0
               have i₂ := b5e16567794 X0 X0
               grind)
            | (have i₁ := b5e1319095 x
               have i₂ := b5e16567794 x x
               grind)
            | exact superpose b5e16567794 b5e1319095
            | (have j1 := b5e16567794 X0 X0
               grind)
            | exact resolve b5e1319095 b5e16567794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1319095 b5e16567794
          have b5e16797770 : ∀ X0 : G, (k x X0) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e48134 x X0
               have i₂ := b5e16797723 X0
               grind)
            | exact superpose b5e16797723 b5e48134
            | (have j1 := b5e16797723 X0
               grind)
            | exact resolve b5e48134 b5e16797723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48134 b5e16797723
          have b5e16797792 : ∀ X0 : G, (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e16797770 X0
               have j1 := b5e40459 x X0
               grind)
            | (have r₁ := b5e16797770 x
               have r₂ := b5e40459 x x
               grind)
            | exact resolve b5e16797770 b5e40459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40459 b5e16797770
          have b5e16797943 : ∀ X0 : G, x = (k X0 x) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e10640371 x X0
               have i₂ := b5e16797792 X0
               grind)
            | exact superpose b5e16797792 b5e10640371
            | (have j0 := b5e10640371 x X0
               grind)
            | exact resolve b5e10640371 b5e16797792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10640371 b5e16797792
          have b5e16798033 : ∀ X0 : G, x = (k X0 x) := by
            intro X0
            first
            | (have j0 := b5e16797943 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16797943
          have b5e16798103 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e341 x X0
               have i₂ := b5e16798033 X0
               grind)
            | exact superpose b5e16798033 b5e341
            | (have j0 := b5e341 x X0
               grind)
            | exact resolve b5e341 b5e16798033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e341 b5e16798033
          have b5e16886394 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ x = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e34 X0 X1 x
               have i₂ := b5e16798103 (M.op X0 X1)
               grind)
            | exact superpose b5e16798103 b5e34
            | (have j1 := b5e16798103 X0
               grind)
            | exact resolve b5e34 b5e16798103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e16798103
          have b5e16886411 : ∀ X0 X1 : G, x = (M.op x X1) ∨ x = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b5e16886394 X0 X1
               have i₂ := b5e33 X1 x X0
               grind)
            | exact superpose b5e33 b5e16886394
            | (have j0 := b5e16886394 X0 X1
               grind)
            | exact resolve b5e16886394 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16886394
          have b5e16950961 : ∀ X0 : G, x = y ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e16886411 y X0
               grind)
            | exact superpose b5e16886411 b5e22
            | (have j1 := b5e16886411 X0 X0
               grind)
            | exact resolve b5e22 b5e16886411
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16886411
          have b5e16950988 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e16950961 X0
               grind)
            | (have r₁ := b5e16950961 X0
               have r₂ := b5e20151
               grind)
            | exact resolve b5e16950961 b5e20151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20151 b5e16950961
          have b5e16951047 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 X0 x
               have i₂ := b5e16950988 X1
               grind)
            | exact superpose b5e16950988 b5e33
            | exact resolve b5e33 b5e16950988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e16950988
          have b5e16951320 : (σ y) ≠ (M.op (σ x) x) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e16951047 (σ x) (σ x)
               grind)
            | exact superpose b5e16951047 b5e23
            | exact resolve b5e23 b5e16951047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16951322 : (σ y) = (M.op (σ x) x) := by
            first
            | (have i₁ := b5e262
               have i₂ := b5e16951047 (σ x) (σ y)
               grind)
            | exact superpose b5e16951047 b5e262
            | exact resolve b5e262 b5e16951047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e262 b5e16951047
          have b5e16951344 : False := by grind
          exact b5e16951344
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ y) = (σ (k x y)) := by
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
        have b6e42 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e12 X2 (M.op X3 X1) X4 (M.op X0 x)
             have i₂ := b6e12 X0 X1 x X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
          intro X1 X2 X3
          first
          | (have i₁ := b6e42 x X1 X2 X3 x
             have i₂ := b6e12 X2 X1 x x
             grind)
          | exact superpose b6e12 b6e42
          | exact resolve b6e42 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e46 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e44 (σ x) X0 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e44
          | exact resolve b6e44 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e92 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e108 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e92
             have r₂ := b6e20
             grind)
          | exact resolve b6e92 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e117 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e108
             have r₂ := b6e21
             grind)
          | exact resolve b6e108 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108
        have b6e245 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e46 (σ x)
             grind)
          | exact superpose b6e46 b6e19
          | exact resolve b6e19 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e267 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e245
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e245
          | exact resolve b6e245 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e245
        have b6e274 : False := by grind
        exact b6e274
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e29 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b7e13 X0 X1 X2 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ x) X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 (M.op X3 X1) X4 (M.op X0 x)
               have i₂ := b7e13 X0 X1 x X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b7e33 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e31 x X1 X2 X3 x
               have i₂ := b7e13 X2 X1 x x
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e34 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e29 X0 x X2 X3 x
               have i₂ := b7e13 X0 X3 x x
               grind)
            | exact superpose b7e13 b7e29
            | exact resolve b7e29 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e35 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e33 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e48 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op (M.op X3 X1) (M.op X3 X1)) ∨ (M.op X0 X2) = (k (M.op X3 X1) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e17 (M.op X3 X1) (M.op X0 X2)
               have i₂ := b7e13 X0 X1 X2 X3
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 (M.op X3 X1) (M.op X0 X2)
               grind)
            | (have r₁ := b7e17 (M.op X3 X1) (M.op X0 X1)
               have r₂ := b7e13 X0 X1 X1 X3
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e52 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (M.op X3 X1) ∨ (M.op X0 X2) = (k (M.op X3 X1) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e48 X0 X1 X2 X3
               have i₂ := b7e13 X3 X1 X1 X3
               grind)
            | exact superpose b7e13 b7e48
            | (have j0 := b7e48 X0 X1 X2 X3
               grind)
            | exact resolve b7e48 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e53 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : (σ y) = (σ (k x y)) := by
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
          have b7e57 : (k x y) = (τ (σ y)) := by
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
          have b7e58 : y = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e71 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X1 X3
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2 X3
               have i₂ := b7e18 X0 (M.op X0 X2)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e77 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e71 X0 X1 X2 x
               have i₂ := b7e33 X2 X0 x
               grind)
            | exact superpose b7e33 b7e71
            | (have j0 := b7e71 X0 X1 X2 x
               grind)
            | exact resolve b7e71 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e90 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
          have b7e91 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e21
               grind)
            | exact resolve b7e90 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e93 : y = (M.op x y) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e22
               grind)
            | exact resolve b7e91 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e122 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e34 x y X0
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e34
            | exact resolve b7e34 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e132 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e198 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (M.op (σ y) (σ y)) ∨ (M.op X0 X1) = (k (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ y) (M.op X0 X1)
               have i₂ := b7e30 X0 X1
               grind)
            | exact superpose b7e30 b7e17
            | (have j0 := b7e17 (σ y) (M.op X0 X1)
               grind)
            | (have r₁ := b7e17 (σ y) (M.op X0 (σ x))
               have r₂ := b7e30 X0 (σ x)
               grind)
            | exact resolve b7e17 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e206 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (σ x)) ∨ (M.op X0 X1) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (k (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e198 X0 X1
               have i₂ := b7e35 (σ y)
               grind)
            | exact superpose b7e35 b7e198
            | (have j0 := b7e198 X0 X1
               grind)
            | (have r₁ := b7e198 X0 (σ y)
               have r₂ := b7e35 X0
               grind)
            | exact resolve b7e198 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e198
          have b7e216 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X1) = (σ y) ∨ (M.op X0 X1) = (k (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e206 X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e206
            | (have j0 := b7e206 X0 X1
               grind)
            | exact resolve b7e206 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e206
          have b7e265 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e132 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e132
            | exact resolve b7e132 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e298 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b7e356 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (M.op (σ X0) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e77 (σ X1) (σ X0) X2
               grind)
            | exact superpose b7e77 b7e19
            | (have j1 := b7e77 (σ X1) (σ X0) X2
               grind)
            | exact resolve b7e19 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e377 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e77 (σ x) X0 (σ x)
               grind)
            | (have i₁ := b7e23
               have i₂ := b7e77 X0 (σ x) (σ x)
               grind)
            | exact superpose b7e77 b7e23
            | (have j1 := b7e77 (σ x) X0 x
               grind)
            | exact resolve b7e23 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e402 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e77 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e403 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e402 X0 X1
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e402 (k X1 X1) X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e402 X1 X0
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e402 (M.op X0 X0) X1
               have r₂ := b7e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b7e402 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e402
          have b7e458 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e403 (σ X1) (σ X0)
               grind)
            | exact superpose b7e403 b7e19
            | (have j1 := b7e403 (σ X1) (σ X0)
               grind)
            | exact resolve b7e19 b7e403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e528 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X2 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e52 X0 X1 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e681 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X1) (σ X0)
               have i₂ := b7e65 X1 X0
               grind)
            | exact superpose b7e65 b7e17
            | (have j0 := b7e17 (σ X1) (σ X0)
               have j1 := b7e65 X1 X0
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X1)
               have r₂ := b7e65 X1 X1
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e65 X0 X1
               grind)
            | exact resolve b7e17 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e684 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 (σ X1) (σ X0)
               have i₂ := b7e65 X0 X1
               grind)
            | exact superpose b7e65 b7e32
            | (have j1 := b7e65 X1 X0
               grind)
            | exact resolve b7e32 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e692 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e65 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e693 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e692 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e692
          have b7e695 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e681 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e681
          have b7e696 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e695 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e695
          have b7e705 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e684 X0 X1
               have i₂ := b7e19 X0 X0
               grind)
            | exact superpose b7e19 b7e684
            | (have j0 := b7e684 X0 X1
               grind)
            | exact resolve b7e684 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e684
          have b7e706 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e696 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e696
            | (have j0 := b7e696 X0 X1
               grind)
            | exact resolve b7e696 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e696
          have b7e1049 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e693 (τ X0)
               have i₂ := b7e27 X0 (τ X0)
               grind)
            | exact superpose b7e27 b7e693
            | (have j0 := b7e693 (τ X0)
               grind)
            | exact resolve b7e693 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1054 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e1049 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1049
            | (have j0 := b7e1049 X0
               grind)
            | exact resolve b7e1049 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1049
          have b7e1058 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1054 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1054
            | (have j0 := b7e1054 X0
               grind)
            | exact resolve b7e1054 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1054
          have b7e3027 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e377 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e377
            | (have j0 := b7e377 (σ y)
               grind)
            | (have r₁ := b7e377 (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e377 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e377
          have b7e3029 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b7e3027
          have b7e3031 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e3029
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e3029
            | exact resolve b7e3029 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3029
          have b7e3034 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e3031
               have i₂ := b7e35 (σ x)
               grind)
            | exact superpose b7e35 b7e3031
            | exact resolve b7e3031 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e3031
          have b7e3630 : (τ (σ x)) = (k x (τ (σ x))) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e298 x
               have i₂ := b7e3034
               grind)
            | exact superpose b7e3034 b7e298
            | exact resolve b7e298 b7e3034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e298
          have b7e3638 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e32 (σ x) (σ x)
               have i₂ := b7e3034
               grind)
            | exact superpose b7e3034 b7e32
            | exact resolve b7e32 b7e3034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3034
          have b7e3663 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e3638
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e3638
            | exact resolve b7e3638 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3638
          have b7e3666 : (σ y) = (σ (k y x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e3630
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e3630
            | exact resolve b7e3630 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3630
          have b7e3968 : (τ (σ y)) = (k y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e3666
               grind)
            | exact superpose b7e3666 b7e14
            | exact resolve b7e14 b7e3666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3666
          have b7e4014 : y = (k y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e3968
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e3968
            | exact resolve b7e3968 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3968
          have b7e4281 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e403 x y
               have i₂ := b7e4014
               grind)
            | exact superpose b7e4014 b7e403
            | (have j0 := b7e403 y x
               grind)
            | exact resolve b7e403 b7e4014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4014
          have b7e4284 : x = (M.op x y) ∨ x = (k x x) := by
            first
            | (have r₁ := b7e4281
               have r₂ := b7e22
               grind)
            | exact resolve b7e4281 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4281
          have b7e4296 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b7e4284
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e4284
            | exact resolve b7e4284 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4284
          have b7e4570 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e693 x
               have i₂ := b7e4296
               grind)
            | exact superpose b7e4296 b7e693
            | (have j0 := b7e693 x
               grind)
            | exact resolve b7e693 b7e4296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4296
          have b7e4579 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
          clear b7e4570
          have b7e5072 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 (σ X1) (σ X1)
               have i₂ := b7e705 X0 X1
               grind)
            | exact superpose b7e705 b7e32
            | (have j1 := b7e705 X0 X1
               grind)
            | exact resolve b7e32 b7e705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e705
          have b7e5117 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e5072 X0 X1
               have i₂ := b7e19 X0 X0
               grind)
            | exact superpose b7e19 b7e5072
            | (have j0 := b7e5072 X0 X1
               grind)
            | exact resolve b7e5072 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5072
          have b7e5118 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e5117 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5117
          have b7e5263 : (σ x) ≠ (σ y) ∨ x = y := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e4579
               grind)
            | exact superpose b7e4579 b7e23
            | exact resolve b7e23 b7e4579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5284 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e216 (σ x) (σ x)
               have i₂ := b7e4579
               grind)
            | exact superpose b7e4579 b7e216
            | exact resolve b7e216 b7e4579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4579
          have b7e5292 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
          clear b7e5284
          have b7e5300 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b7e5292
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e5292
            | exact resolve b7e5292 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5292
          have b7e5308 : (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have r₁ := b7e5300
               have r₂ := b7e5263
               grind)
            | exact resolve b7e5300 b7e5263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5263 b7e5300
          have b7e5538 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b7e706
          have b7e5593 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e5538 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e5538
            | (have j0 := b7e5538 X0 X1
               grind)
            | exact resolve b7e5538 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5538
          have b7e5594 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e5593 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5593
          have b7e6095 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e356 X1 X0 (σ X1)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e356
          have b7e6282 : (k y x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e5308
               grind)
            | exact superpose b7e5308 b7e14
            | exact resolve b7e14 b7e5308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5308
          have b7e6338 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b7e6282
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e6282
            | exact resolve b7e6282 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6282
          have b7e10090 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e3663
               grind)
            | exact superpose b7e3663 b7e14
            | exact resolve b7e14 b7e3663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3663
          have b7e10181 : (σ x) = (σ (k x x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e10090
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e10090
            | exact resolve b7e10090 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10090
          have b7e10789 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e693 x
               have i₂ := b7e10181
               grind)
            | exact superpose b7e10181 b7e693
            | (have j0 := b7e693 x
               grind)
            | (have r₁ := b7e693 x
               have r₂ := b7e10181
               grind)
            | exact resolve b7e693 b7e10181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e693 b7e10181
          have b7e10836 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by grind
          clear b7e10789
          have b7e11443 : (σ x) ≠ (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e10836
               grind)
            | exact superpose b7e10836 b7e23
            | exact resolve b7e23 b7e10836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e11470 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e216 (σ x) (σ x)
               have i₂ := b7e10836
               grind)
            | exact superpose b7e10836 b7e216
            | exact resolve b7e216 b7e10836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216 b7e10836
          have b7e11486 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
          clear b7e11470
          have b7e11495 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e11486
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e11486
            | exact resolve b7e11486 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11486
          have b7e11500 : (σ x) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b7e11495
               have r₂ := b7e11443
               grind)
            | exact resolve b7e11495 b7e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11443 b7e11495
          have b7e12672 : (k y x) = (τ (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e11500
               grind)
            | exact superpose b7e11500 b7e14
            | exact resolve b7e14 b7e11500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11500
          have b7e12736 : y = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b7e12672
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e12672
            | exact resolve b7e12672 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12672
          have b7e13424 : x ≠ y ∨ x = (k y x) := by grind
          clear b7e12736
          have b7e13426 : x = (k y x) := by
            first
            | (have r₁ := b7e13424
               have r₂ := b7e6338
               grind)
            | exact resolve b7e13424 b7e6338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6338 b7e13424
          have b7e21742 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e26 X0 (τ X0)
               have i₂ := b7e5118 (τ X0) X1
               grind)
            | exact superpose b7e5118 b7e26
            | (have j1 := b7e5118 (τ X0) X1
               grind)
            | exact resolve b7e26 b7e5118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5118
          have b7e21983 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e21742 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e21742
            | (have j0 := b7e21742 X0 X1
               grind)
            | exact resolve b7e21742 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21742
          have b7e22055 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e21983 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e21983
            | (have j0 := b7e21983 X0 X1
               grind)
            | exact resolve b7e21983 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e21983
          have b7e22076 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e22055 X0 X1
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e22055
            | (have j0 := b7e22055 X0 X1
               grind)
            | exact resolve b7e22055 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22055
          have b7e22212 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e5594 (τ X0) X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e5594
            | exact resolve b7e5594 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5594
          have b7e22434 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e22212 X0 X1
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e22212
            | (have j0 := b7e22212 X0 X1
               grind)
            | exact resolve b7e22212 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22212
          have b7e22474 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e22434 X0 X1
               have i₂ := b7e27 X0 X1
               grind)
            | exact superpose b7e27 b7e22434
            | (have j0 := b7e22434 X0 X1
               grind)
            | exact resolve b7e22434 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22434
          have b7e23115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e22076 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e22076
            | (have j0 := b7e22076 X1 X1
               grind)
            | exact resolve b7e22076 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e23235 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e403 X0 X0
               have i₂ := b7e22076 X0 X1
               grind)
            | exact superpose b7e22076 b7e403
            | (have j0 := b7e403 X0 (σ X1)
               have j1 := b7e22076 X0 X1
               grind)
            | exact resolve b7e403 b7e22076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22076
          have b7e23282 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b7e23235 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23235
          have b7e23703 : x = (M.op y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e13426
               have i₂ := b7e23115 y x
               grind)
            | exact superpose b7e23115 b7e13426
            | (have j1 := b7e23115 x x
               grind)
            | exact resolve b7e13426 b7e23115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13426
          have b7e23724 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e403 X0 X0
               have i₂ := b7e23115 X1 X0
               grind)
            | exact superpose b7e23115 b7e403
            | (have j0 := b7e403 X0 X1
               have j1 := b7e23115 X1 X0
               grind)
            | exact resolve b7e403 b7e23115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e23759 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e26 X0 (τ X0)
               have i₂ := b7e23115 X1 (τ X0)
               grind)
            | exact superpose b7e23115 b7e26
            | (have j1 := b7e23115 X1 (τ X0)
               grind)
            | exact resolve b7e26 b7e23115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e23772 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e23724 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23724
          have b7e23816 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e23759 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e23759
            | (have j0 := b7e23759 X0 X1
               grind)
            | exact resolve b7e23759 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23759
          have b7e23842 : x = (M.op x x) ∨ x = (k x x) := by
            first
            | (have i₁ := b7e23703
               have i₂ := b7e122 x
               grind)
            | exact superpose b7e122 b7e23703
            | exact resolve b7e23703 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23703
          have b7e23904 : x = (M.op x x) := by
            first
            | (have j1 := b7e1058 x
               grind)
            | (have r₁ := b7e23842
               have r₂ := b7e1058 x
               grind)
            | exact resolve b7e23842 b7e1058
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1058 b7e23842
          have b7e24399 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e23904
               grind)
            | exact superpose b7e23904 b7e21
            | exact resolve b7e21 b7e23904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31601 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e27 X1 X0
               have i₂ := b7e23816 X1 X0
               grind)
            | exact superpose b7e23816 b7e27
            | (have j1 := b7e23816 X1 X1
               grind)
            | exact resolve b7e27 b7e23816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e23816
          have b7e67976 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e22474 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e22474
            | exact resolve b7e22474 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e22474
          have b7e68878 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e67976 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69248 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X0 X2) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e68878 (M.op X0 X2) X1
               have i₂ := b7e34 X0 X2 X1
               grind)
            | exact superpose b7e34 b7e68878
            | (have j0 := b7e68878 X0 X1
               grind)
            | exact resolve b7e68878 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e192797 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op x (τ X0))) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e31601 y X0
               have i₂ := b7e122 (τ X0)
               grind)
            | exact superpose b7e122 b7e31601
            | (have j0 := b7e31601 X0 X0
               grind)
            | exact resolve b7e31601 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e250002 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e31601 x X0
               have i₂ := b7e192797 X0
               grind)
            | exact superpose b7e192797 b7e31601
            | (have j0 := b7e31601 X0 X0
               have j1 := b7e192797 X0
               grind)
            | exact resolve b7e31601 b7e192797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31601 b7e192797
          have b7e250489 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e250002 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e250002
          have b7e255991 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ x) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e23115 (σ y) X0
               have i₂ := b7e250489 X0
               grind)
            | exact superpose b7e250489 b7e23115
            | (have j0 := b7e23115 X0 X0
               have j1 := b7e250489 X0
               grind)
            | exact resolve b7e23115 b7e250489
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e250489
          have b7e256206 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ x) X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e255991 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e255991
          have b7e273767 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e23115 (σ x) X0
               have i₂ := b7e256206 X0
               grind)
            | exact superpose b7e256206 b7e23115
            | (have j0 := b7e23115 X0 X0
               have j1 := b7e256206 X0
               grind)
            | exact resolve b7e23115 b7e256206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23115 b7e256206
          have b7e273987 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e273767 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e273767
          have b7e308315 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ x) X0) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e34 (σ y) X0 X1
               have i₂ := b7e273987 X0
               grind)
            | exact superpose b7e273987 b7e34
            | (have j1 := b7e273987 X0
               grind)
            | exact resolve b7e34 b7e273987
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e273987
          have b7e308774 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ x) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e308315 X0 X1
               have i₂ := b7e34 (σ x) X0 X1
               grind)
            | exact superpose b7e34 b7e308315
            | (have j0 := b7e308315 X0 X1
               grind)
            | exact resolve b7e308315 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e308315
          have b7e331577 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e308774 X0 (σ x)
               grind)
            | exact superpose b7e308774 b7e24
            | (have j1 := b7e308774 X0 x
               grind)
            | exact resolve b7e24 b7e308774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e308774
          have b7e332028 : ∀ X0 : G, (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e331577 X0
               grind)
            | (have r₁ := b7e331577 X0
               have r₂ := b7e23
               grind)
            | exact resolve b7e331577 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e331577
          have b7e335390 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e23772 X0 X0
               have i₂ := b7e332028 X0
               grind)
            | exact superpose b7e332028 b7e23772
            | (have j0 := b7e23772 X0 x
               grind)
            | exact resolve b7e23772 b7e332028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23772
          have b7e335466 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e23282 (σ X0) X0
               have i₂ := b7e332028 (σ X0)
               grind)
            | exact superpose b7e332028 b7e23282
            | (have j0 := b7e23282 (σ X0) x
               grind)
            | exact resolve b7e23282 b7e332028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23282 b7e332028
          have b7e335549 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e335466 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e335466
          have b7e335558 : ∀ X0 : G, (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e335390 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e335390
          have b7e339355 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e528 X0 X0 x
               have i₂ := b7e335558 X0
               grind)
            | exact superpose b7e335558 b7e528
            | exact resolve b7e528 b7e335558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e528
          have b7e339687 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e339355 X0 X1
               have j1 := b7e69248 X1 X0 X0
               grind)
            | (have r₁ := b7e339355 X1 X0
               have r₂ := b7e69248 X0 X1 x
               grind)
            | exact resolve b7e339355 b7e69248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69248 b7e339355
          have b7e348776 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (k (M.op X0 X1) (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e339687 (M.op X3 X1) (M.op X0 x)
               have i₂ := b7e13 X0 X1 x X3
               grind)
            | exact superpose b7e13 b7e339687
            | exact resolve b7e339687 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e349090 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e132 (M.op X1 (σ X0)) X0
               have i₂ := b7e339687 (σ X0) X1
               grind)
            | exact superpose b7e339687 b7e132
            | exact resolve b7e132 b7e339687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e132 b7e339687
          have b7e349191 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e349090 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e349090
            | exact resolve b7e349090 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e349090
          have b7e352909 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (M.op (σ (τ X1)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e6095 (τ X0) (τ X1)
               have i₂ := b7e265 X1 X0
               grind)
            | exact superpose b7e265 b7e6095
            | (have j0 := b7e6095 (τ X0) (τ X1)
               grind)
            | exact resolve b7e6095 b7e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e265 b7e6095
          have b7e353720 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e352909 X0 X1
               have i₂ := b7e335549 (τ X1)
               grind)
            | exact superpose b7e335549 b7e352909
            | (have j0 := b7e352909 X0 X1
               grind)
            | exact resolve b7e352909 b7e335549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e335549 b7e352909
          have b7e353987 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (M.op (σ (τ X1)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e353720 X0 X1
               have i₂ := b7e15 (k X0 X1)
               grind)
            | exact superpose b7e15 b7e353720
            | (have j0 := b7e353720 X0 X1
               grind)
            | exact resolve b7e353720 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e353720
          have b7e354180 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X1)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e353987 X0 X1
               have i₂ := b7e15 X1
               grind)
            | exact superpose b7e15 b7e353987
            | (have j0 := b7e353987 X0 X1
               grind)
            | exact resolve b7e353987 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e353987
          have b7e354281 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e354180 X0 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e354180
            | (have j0 := b7e354180 X0 X1
               grind)
            | exact resolve b7e354180 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354180
          have b7e354351 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e354281 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e354281
            | (have j0 := b7e354281 X0 X1
               grind)
            | exact resolve b7e354281 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354281
          have b7e354396 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e354351 X0 X1
               have i₂ := b7e335558 X1
               grind)
            | exact superpose b7e335558 b7e354351
            | (have j0 := b7e354351 X0 X1
               grind)
            | exact resolve b7e354351 b7e335558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354351
          have b7e354431 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e354396 X0 X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e354396
            | (have j0 := b7e354396 X0 X1
               grind)
            | exact resolve b7e354396 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354396
          have b7e354454 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e354431 X0 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e354431
            | (have j0 := b7e354431 X0 X1
               grind)
            | exact resolve b7e354431 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354431
          have b7e361873 : ∀ X0 : G, y = (k (τ (M.op X0 (σ x))) y) := by
            intro X0
            first
            | (have i₁ := b7e349191 y (M.op X0 x)
               have i₂ := b7e30 X0 x
               grind)
            | exact superpose b7e30 b7e349191
            | exact resolve b7e349191 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e349191
          have b7e378692 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e348776 X0 X0 X1
               have i₂ := b7e335558 X0
               grind)
            | exact superpose b7e335558 b7e348776
            | exact resolve b7e348776 b7e335558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e335558 b7e348776
          have b7e381977 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e145 X1 (M.op X0 (σ X1))
               have i₂ := b7e378692 (σ X1) X0
               grind)
            | exact superpose b7e378692 b7e145
            | exact resolve b7e145 b7e378692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e145 b7e378692
          have b7e429369 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e381977 (σ X1) X0
               have i₂ := b7e458 X0 X1
               grind)
            | exact superpose b7e458 b7e381977
            | (have j1 := b7e458 X1 X0
               grind)
            | exact resolve b7e381977 b7e458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e458 b7e381977
          have b7e429566 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e429369 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e429369
            | (have j0 := b7e429369 X0 X1
               grind)
            | exact resolve b7e429369 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e429369
          have b7e1541837 : ∀ X0 : G, y = (k (τ (σ (k X0 x))) y) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e361873 (σ X0)
               have i₂ := b7e429566 x X0
               grind)
            | exact superpose b7e429566 b7e361873
            | (have j1 := b7e429566 y (τ (σ (k X0 x)))
               grind)
            | exact resolve b7e361873 b7e429566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e361873 b7e429566
          have b7e1541998 : ∀ X0 : G, y = (k (k X0 x) y) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e1541837 X0
               have i₂ := b7e14 (k X0 x)
               grind)
            | exact superpose b7e14 b7e1541837
            | (have j0 := b7e1541837 X0
               grind)
            | exact resolve b7e1541837 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1541837
          have b7e1552706 : ∀ X0 : G, y = (k (M.op X0 x) y) ∨ x = (M.op X0 x) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e1541998 X0
               have i₂ := b7e67976 X0 x
               grind)
            | exact superpose b7e67976 b7e1541998
            | (have j0 := b7e1541998 X0
               have j1 := b7e67976 (M.op X0 x) y
               grind)
            | exact resolve b7e1541998 b7e67976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67976 b7e1541998
          have b7e1552801 : ∀ X0 : G, y = (k (M.op X0 x) y) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have j0 := b7e1552706 X0
               have j1 := b7e68878 (M.op X0 x) y
               grind)
            | (have r₁ := b7e1552706 X0
               have r₂ := b7e68878 X0 x
               grind)
            | exact resolve b7e1552706 b7e68878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68878 b7e1552706
          have b7e1560212 : ∀ X0 X1 : G, y = (k (M.op X0 x) y) ∨ x = (k (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e1552801 (M.op X0 X1)
               have i₂ := b7e34 X0 X1 x
               grind)
            | exact superpose b7e34 b7e1552801
            | (have j0 := b7e1552801 X0
               grind)
            | exact resolve b7e1552801 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1552801
          have b7e1589756 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) y) ∨ y = (M.op y (M.op X0 x)) ∨ x = (k (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e403 y (M.op X0 x)
               have i₂ := b7e1560212 X0 X1
               grind)
            | exact superpose b7e1560212 b7e403
            | (have j0 := b7e403 y (M.op X0 x)
               have j1 := b7e1560212 X0 X1
               grind)
            | exact resolve b7e403 b7e1560212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e403 b7e1560212
          have b7e1589808 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op y (M.op X0 x)) ∨ x = (k (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e1589756 X0 X1
               have i₂ := b7e34 X0 x y
               grind)
            | exact superpose b7e34 b7e1589756
            | (have j0 := b7e1589756 X0 X1
               grind)
            | exact resolve b7e1589756 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1589756
          have b7e1589823 : ∀ X0 X1 : G, y = (M.op y x) ∨ y = (M.op X0 y) ∨ x = (k (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e1589808 X0 X1
               have i₂ := b7e33 x y X0
               grind)
            | exact superpose b7e33 b7e1589808
            | (have j0 := b7e1589808 X0 X1
               grind)
            | exact resolve b7e1589808 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1589808
          have b7e1589826 : ∀ X0 X1 : G, x = (k (M.op X0 X1) x) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have j0 := b7e1589823 X0 X1
               grind)
            | (have r₁ := b7e1589823 X0 X1
               have r₂ := b7e22
               grind)
            | exact resolve b7e1589823 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1589823
          have b7e1590786 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op X0 X1) x) ∨ x = (M.op x (M.op X0 X1)) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e354454 (M.op X0 X1) x
               have i₂ := b7e1589826 X0 X1
               grind)
            | exact superpose b7e1589826 b7e354454
            | (have j0 := b7e354454 (M.op X0 X1) x
               have j1 := b7e1589826 X0 X1
               grind)
            | (have r₁ := b7e354454 (M.op X0 X1) x
               have r₂ := b7e1589826 X0 X1
               grind)
            | exact resolve b7e354454 b7e1589826
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e354454 b7e1589826
          have b7e1590803 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) x) ∨ x = (M.op x (M.op X0 X1)) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have j0 := b7e1590786 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1590786
          have b7e1590806 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ x = (M.op x (M.op X0 X1)) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e1590803 X0 X1
               have i₂ := b7e34 X0 X1 x
               grind)
            | exact superpose b7e34 b7e1590803
            | (have j0 := b7e1590803 X0 X1
               grind)
            | exact resolve b7e1590803 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1590803
          have b7e1590819 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ x = (M.op x X1) ∨ x = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e1590806 X0 X1
               have i₂ := b7e33 X1 x X0
               grind)
            | exact superpose b7e33 b7e1590806
            | (have j0 := b7e1590806 X0 X1
               grind)
            | exact resolve b7e1590806 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e1590806
          have b7e3349277 : ∀ X0 : G, x = y ∨ y = (M.op X0 y) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e93
               have i₂ := b7e1590819 X0 y
               grind)
            | exact superpose b7e1590819 b7e93
            | (have j1 := b7e1590819 X0 x
               grind)
            | exact resolve b7e93 b7e1590819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e1590819
          have b7e3349284 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b7e3349277 X0
               grind)
            | (have r₁ := b7e3349277 X0
               have r₂ := b7e24399
               grind)
            | exact resolve b7e3349277 b7e24399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24399 b7e3349277
          have b7e3359046 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y X1) ∨ x = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 y X1
               have i₂ := b7e3349284 X0
               grind)
            | exact superpose b7e3349284 b7e34
            | (have j1 := b7e3349284 X0
               grind)
            | exact resolve b7e34 b7e3349284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3349284
          have b7e3359132 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) ∨ x = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e3359046 X0 X1
               have i₂ := b7e122 X1
               grind)
            | exact superpose b7e122 b7e3359046
            | (have j0 := b7e3359046 X0 X1
               grind)
            | exact resolve b7e3359046 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122 b7e3359046
          have b7e3361495 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e23904
               have i₂ := b7e3359132 X0 x
               grind)
            | (have i₁ := b7e23904
               have i₂ := b7e3359132 x x
               grind)
            | exact superpose b7e3359132 b7e23904
            | (have j1 := b7e3359132 X0 x
               grind)
            | exact resolve b7e23904 b7e3359132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23904 b7e3359132
          have b7e3361638 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b7e3361495 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3361495
          have b7e3380673 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 x X1
               have i₂ := b7e3361638 X0
               grind)
            | exact superpose b7e3361638 b7e34
            | exact resolve b7e34 b7e3361638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e3361638
          have b7e3507012 : (σ y) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e3380673 (σ x) (σ x)
               grind)
            | exact superpose b7e3380673 b7e23
            | exact resolve b7e23 b7e3380673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3507013 : (σ y) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e3380673 (σ y) (σ x)
               grind)
            | exact superpose b7e3380673 b7e24
            | exact resolve b7e24 b7e3380673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3380673
          have b7e3507336 : False := by grind
          exact b7e3507336
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e81 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e172 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e81 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e173 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e172
               have r₂ := b8e24
               grind)
            | exact resolve b8e172 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e172
          have b8e174 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e173
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e173
            | exact resolve b8e173 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e175 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e174
               grind)
            | exact superpose b8e174 b8e20
            | exact resolve b8e20 b8e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e204 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e175
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e175
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e175 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175
          have b8e205 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e204
          have b8e207 : y = (M.op y x) := by
            first
            | (have r₁ := b8e205
               have r₂ := b8e21
               grind)
            | exact resolve b8e205 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e205
          have b8e209 : False := by grind
          exact b8e209

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_Equation727 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e42 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e144 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e42 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e409 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e43 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e411 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e409
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e409
        | exact resolve b0e409 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e409
      have b0e419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e411
           have i₂ := b0e144
           grind)
        | exact superpose b0e144 b0e411
        | exact resolve b0e411 b0e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144 b0e411
      have b0e422 : False := by grind
      exact b0e422
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b2e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e53 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e53
          | exact resolve b2e53 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e53
        have b2e126 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e60 y
             grind)
          | exact superpose b2e60 b2e21
          | exact resolve b2e21 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e132 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e126
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e126
          | exact resolve b2e126 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126
        have b2e133 : False := by grind
        exact b2e133
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e51 (σ X0)
             grind)
          | exact superpose b6e51 b6e18
          | exact resolve b6e18 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e53 X0
             have i₂ := b6e51 X0
             grind)
          | exact superpose b6e51 b6e53
          | exact resolve b6e53 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e53
        have b6e138 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e60 y
             grind)
          | exact superpose b6e60 b6e22
          | exact resolve b6e22 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e146 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e138
             have i₂ := b6e60 x
             grind)
          | exact superpose b6e60 b6e138
          | exact resolve b6e138 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e138
        have b6e185 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e146
             grind)
          | exact superpose b6e146 b6e13
          | exact resolve b6e13 b6e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146
        have b6e186 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e185
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e185
          | exact resolve b6e185 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e185
        have b6e192 : False := by grind
        exact b6e192
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e44
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e66 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 y X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 y X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e75 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e75
            | (have j0 := b8e75 X0 X1
               grind)
            | exact resolve b8e75 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e136 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e66 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e137 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e136
               have r₂ := b8e22
               grind)
            | exact resolve b8e136 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e192 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e23
            | exact resolve b8e23 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e203 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e192
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e192
            | exact resolve b8e192 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e192
          have b8e816 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e77 x y
               grind)
            | exact superpose b8e77 b8e20
            | (have j1 := b8e77 x y
               grind)
            | exact resolve b8e20 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e863 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e816
               have r₂ := b8e203
               grind)
            | exact resolve b8e816 b8e203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203 b8e816
          have b8e879 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e863
               have r₂ := b8e24
               grind)
            | exact resolve b8e863 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e863
          have b8e890 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e879
               have i₂ := b8e137
               grind)
            | exact superpose b8e137 b8e879
            | exact resolve b8e879 b8e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137 b8e879
          have b8e891 : False := by grind
          exact b8e891

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation727 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : (M.op x x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x x) X0))) = X0 := by
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
          have b4e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
               have i₂ := b4e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e137 : ∀ X0 X1 : G, (M.op (M.op x x) (M.op (M.op X1 (M.op x x)) X0)) = (M.op y (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 (M.op (M.op x x) (M.op (M.op X1 (M.op x x)) X0))
               have i₂ := b4e13 X0 (M.op x x) X1
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e141 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e137 X0 x
               have i₂ := b4e41 X0 x x x
               grind)
            | exact superpose b4e41 b4e137
            | exact resolve b4e137 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e199 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3)) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e41 X3 (M.op (M.op X2 X1) X0) X1 X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e41
            | exact resolve b4e41 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e211 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X2 X0) x
               have i₂ := b4e41 X1 X0 X2 x
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e404 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e211 y y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e211
            | exact resolve b4e211 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e405 : ∀ X0 X1 : G, (M.op y (M.op (M.op x x) X0)) = (M.op (M.op X1 y) (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e211 y (M.op y (M.op (M.op x x) X0)) X1
               have i₂ := b4e39 X0
               grind)
            | exact superpose b4e39 b4e211
            | exact resolve b4e211 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e407 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e211 X2 (M.op (M.op X3 X2) X0) X1
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e211
            | exact resolve b4e211 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e410 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op x (M.op x X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e211 y X0 X1
               have i₂ := b4e141 X0
               grind)
            | exact superpose b4e141 b4e211
            | exact resolve b4e211 b4e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141
          have b4e418 : y = (M.op y (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b4e404 x
               have i₂ := b4e405 (M.op x x) x
               grind)
            | exact superpose b4e405 b4e404
            | exact resolve b4e404 b4e405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e404 b4e405
          have b4e666 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X0)) X1)) X5) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e407 X5 X2 (M.op (M.op X3 (M.op X4 X0)) X1) (M.op X4 X0)
               have i₂ := b4e41 X1 X0 X4 X3
               grind)
            | exact superpose b4e41 b4e407
            | exact resolve b4e407 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e667 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e407 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
               have i₂ := b4e211 X2 X0 x
               grind)
            | exact superpose b4e211 b4e407
            | exact resolve b4e407 b4e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e211
          have b4e1069 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op x (M.op x X0)) (M.op X0 X2)) (M.op (M.op (M.op x (M.op x X0)) (M.op X0 X2)) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e40 X0 (M.op x (M.op x X0)) (M.op x y) X3
               have i₂ := b4e410 X0 x
               grind)
            | exact superpose b4e410 b4e40
            | exact resolve b4e40 b4e410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e410
          have b4e1078 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op x X0) (M.op (M.op x (M.op x X0)) (M.op X0 X2))) (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e1069 X0 X2 X3
               have i₂ := b4e199 (M.op X0 X2) (M.op x X0) x (M.op X2 X3)
               grind)
            | exact superpose b4e199 b4e1069
            | exact resolve b4e1069 b4e199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e199 b4e1069
          have b4e1080 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op X0 (M.op X0 X2))) (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e1078 X0 X2 X3
               have i₂ := b4e666 X0 (M.op X0 X2) (M.op x X0) x x (M.op (M.op X0 X2) (M.op X2 X3))
               grind)
            | exact superpose b4e666 b4e1078
            | exact resolve b4e1078 b4e666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e666 b4e1078
          have b4e1081 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X0 X2) (M.op X2 X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e1080 X0 X2 X3
               have i₂ := b4e667 X2 X0 X0 (M.op (M.op X0 X2) (M.op X2 X3))
               grind)
            | exact superpose b4e667 b4e1080
            | exact resolve b4e1080 b4e667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e667 b4e1080
          have b4e1171 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 x) (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e418
               have i₂ := b4e407 (M.op x x) x x X0
               grind)
            | (have i₁ := b4e418
               have i₂ := b4e407 (M.op x x) X0 x x
               grind)
            | exact superpose b4e407 b4e418
            | exact resolve b4e418 b4e407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e418
          have b4e1720 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X3 X0))) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e407 X4 X1 (M.op (M.op X2 X3) (M.op X3 X0)) X3
               have i₂ := b4e1081 X2 X3 X0
               grind)
            | exact superpose b4e1081 b4e407
            | exact resolve b4e407 b4e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2405 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op X0 (M.op (M.op X1 x) (M.op x x))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e407 X2 X0 (M.op (M.op X1 x) (M.op x x)) y
               have i₂ := b4e1171 X1
               grind)
            | exact superpose b4e1171 b4e407
            | exact resolve b4e407 b4e1171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e407
          have b4e2409 : ∀ X2 : G, (M.op x X2) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b4e2405 x x X2
               have i₂ := b4e1720 x x x x X2
               grind)
            | exact superpose b4e1720 b4e2405
            | exact resolve b4e2405 b4e1720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1720 b4e2405
          have b4e2775 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e1171 X0
               have i₂ := b4e2409 (M.op (M.op X0 x) (M.op x x))
               grind)
            | exact superpose b4e2409 b4e1171
            | exact resolve b4e1171 b4e2409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1171 b4e2409
          have b4e2838 : x = y := by
            first
            | (have i₁ := b4e2775 x
               have i₂ := b4e1081 x x x
               grind)
            | (have i₁ := b4e2775 x
               have i₂ := b4e1081 x x (M.op x (M.op (M.op x x) (M.op x x)))
               grind)
            | exact superpose b4e1081 b4e2775
            | exact resolve b4e2775 b4e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1081 b4e2775
          have b4e2862 : False := by grind
          exact b4e2862
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
          have b8e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e78 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
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
          have b8e89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e147 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e78 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e148 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e147
               have r₂ := b8e21
               grind)
            | exact resolve b8e147 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
          have b8e578 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e535
               have r₂ := b8e57
               grind)
            | exact resolve b8e535 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57 b8e535
          have b8e593 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e578
               have r₂ := b8e23
               grind)
            | exact resolve b8e578 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e578
          have b8e604 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e593
               have i₂ := b8e148
               grind)
            | exact superpose b8e148 b8e593
            | exact resolve b8e593 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148 b8e593
          have b8e605 : False := by grind
          exact b8e605

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e42 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k x y) := by
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
      have b0e43 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e45 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e43
      have b0e46 : (M.op x y) = (k x y) := by grind
      clear b0e42
      have b0e47 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
      have b0e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
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
      have b0e49 : False := by grind
      exact b0e49
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k x y) := by
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
        have b2e52 : (M.op x y) = (k x y) := by grind
        clear b2e50
        have b2e78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X0 X0) (M.op X1 X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e78 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78
        have b2e83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e82 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e83 (σ X0) (σ X1)
             grind)
          | exact superpose b2e83 b2e18
          | (have j1 := b2e83 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83
        have b2e728 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e90 x y
             grind)
          | exact superpose b2e90 b2e19
          | (have j1 := b2e90 x y
             grind)
          | exact resolve b2e19 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e747 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e728
             have r₂ := b2e22
             grind)
          | exact resolve b2e728 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e728
        have b2e753 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e747
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e747
          | exact resolve b2e747 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e747
        have b2e754 : False := by grind
        exact b2e754
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e52 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b6e79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X0 X0) (M.op X1 X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e79 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e83 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e88 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e19
          | exact resolve b6e19 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e96 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e88
             have i₂ := b6e84 x y
             grind)
          | exact superpose b6e84 b6e88
          | (have j1 := b6e84 x y
             grind)
          | (have r₁ := b6e88
             have r₂ := b6e84 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e88
             have r₂ := b6e84 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e88 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e88
        have b6e99 : x = y := by grind
        clear b6e96
        have b6e101 : False := by grind
        exact b6e101
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X1 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e67 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e68 (σ X0) (σ X1)
               grind)
            | exact superpose b8e68 b8e19
            | (have j1 := b8e68 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e681 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e73 x y
               grind)
            | exact superpose b8e73 b8e20
            | (have j1 := b8e73 x y
               grind)
            | exact resolve b8e20 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e700 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e681
               have r₂ := b8e24
               grind)
            | exact resolve b8e681 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e681
          have b8e706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e700
               have i₂ := b8e68 x y
               grind)
            | exact superpose b8e68 b8e700
            | (have j1 := b8e68 x y
               grind)
            | (have r₁ := b8e700
               have r₂ := b8e68 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e700
               have r₂ := b8e68 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e700 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68 b8e700
          have b8e709 : x = y := by grind
          clear b8e706
          have b8e711 : False := by grind
          exact b8e711
