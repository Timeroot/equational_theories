import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation3587 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
      have b0e82 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e86 : False := by grind
      exact b0e86
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e13 y x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e33
            | exact resolve b4e33 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e39 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e32 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e60 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e38 (σ x)
               grind)
            | exact superpose b4e38 b4e20
            | exact resolve b4e20 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e61 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e60
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e60
            | exact resolve b4e60 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e60
          have b4e62 : False := by grind
          exact b4e62
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e13 y x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b5e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
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
          have b5e37 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e32 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e102 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 (σ X0) (σ X0) x
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e35
            | exact resolve b5e35 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e35
          have b5e204 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e102 y x
               have i₂ := b5e37 y
               grind)
            | exact superpose b5e37 b5e102
            | exact resolve b5e102 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e235 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e204 (σ x)
               grind)
            | exact superpose b5e204 b5e20
            | exact resolve b5e20 b5e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e204
          have b5e239 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e235
               have i₂ := b5e37 x
               grind)
            | exact superpose b5e37 b5e235
            | exact resolve b5e235 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e235
          have b5e240 : False := by grind
          exact b5e240
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ x) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b7e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e34 X0 X1 x X3
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e37 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e32 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e40 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e37 (σ x)
               grind)
            | exact superpose b7e37 b7e20
            | exact resolve b7e20 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e114 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e37 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e37
            | exact resolve b7e37 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e37
          have b7e170 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e114
               grind)
            | exact superpose b7e114 b7e14
            | exact resolve b7e14 b7e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e171 : y = (M.op y y) := by
            first
            | (have i₁ := b7e170
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e170
            | exact resolve b7e170 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e170
          have b7e195 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e35 y y x
               have i₂ := b7e171
               grind)
            | exact superpose b7e171 b7e35
            | exact resolve b7e35 b7e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e171
          have b7e231 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e195 x
               grind)
            | exact superpose b7e195 b7e40
            | exact resolve b7e40 b7e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e195
          have b7e232 : False := by grind
          exact b7e232
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b8e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e33 X0 X1 x X3
               have i₂ := b8e13 X0 X1 x
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e39 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e34 (M.op X0 X1) X1 x
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 (M.op X0 X1)
               have i₂ := b8e39 X0 X1
               grind)
            | exact superpose b8e39 b8e17
            | (have j0 := b8e17 (M.op X0 X1) X1
               grind)
            | (have r₁ := b8e17 X1 (M.op X0 X1)
               have r₂ := b8e39 X0 X1
               grind)
            | exact resolve b8e17 b8e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e58 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e62 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b8e63 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e18 (τ X1) X0
               grind)
            | exact superpose b8e18 b8e26
            | (have j1 := b8e18 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e62 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e62
            | exact resolve b8e62 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e67
          have b8e85 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 (σ X0) (σ X0) x
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e34
            | exact resolve b8e34 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e95 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e98 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 (σ X0) (σ X1) x
               have i₂ := b8e60 X0 X1
               grind)
            | exact superpose b8e60 b8e34
            | (have j1 := b8e60 X1 X0
               grind)
            | exact resolve b8e34 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e104 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e95
               have r₂ := b8e23
               grind)
            | exact resolve b8e95 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95
          have b8e123 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e68 X0
               grind)
            | exact superpose b8e68 b8e14
            | exact resolve b8e14 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e156 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e85 (M.op X0 X1) X1
               have i₂ := b8e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b8e34 b8e85
            | exact resolve b8e85 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e219 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 (τ X0) (τ X0) x
               have i₂ := b8e123 X0
               grind)
            | exact superpose b8e123 b8e34
            | exact resolve b8e34 b8e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e309 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e219 (M.op X0 X1) X1
               have i₂ := b8e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b8e34 b8e219
            | exact resolve b8e219 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e219
          have b8e403 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e104
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e104
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e104
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e104
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e104 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e404 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e403
          have b8e405 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e404
               have r₂ := b8e21
               grind)
            | exact resolve b8e404 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e404
          have b8e490 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e63 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e63
            | exact resolve b8e63 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e526 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e490 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e490
            | (have j0 := b8e490 X0 X1
               grind)
            | exact resolve b8e490 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490
          have b8e705 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e58 (σ x) (σ y)
               have i₂ := b8e405
               grind)
            | exact superpose b8e405 b8e58
            | exact resolve b8e58 b8e405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e405
          have b8e710 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e705
               have r₂ := b8e23
               grind)
            | exact resolve b8e705 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e705
          have b8e714 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e710
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e710
            | exact resolve b8e710 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e710
          have b8e2911 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e526 y x
               have i₂ := b8e714
               grind)
            | exact superpose b8e714 b8e526
            | (have j0 := b8e526 y x
               grind)
            | exact resolve b8e526 b8e714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e526 b8e714
          have b8e2949 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e2911
          have b8e2970 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e2949
               have r₂ := b8e21
               grind)
            | exact resolve b8e2949 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2949
          have b8e4130 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e156 x y x
               have i₂ := b8e2970
               grind)
            | exact superpose b8e2970 b8e156
            | exact resolve b8e156 b8e2970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e4369 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e4130 (σ x)
               grind)
            | exact superpose b8e4130 b8e20
            | exact resolve b8e20 b8e4130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4130
          have b8e4380 : x = (M.op x y) := by
            first
            | (have r₁ := b8e4369
               have r₂ := b8e2970
               grind)
            | exact resolve b8e4369 b8e2970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2970 b8e4369
          have b8e4545 : y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e58 x y
               have i₂ := b8e4380
               grind)
            | exact superpose b8e4380 b8e58
            | exact resolve b8e58 b8e4380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e4550 : y = (k y x) := by
            first
            | (have r₁ := b8e4545
               have r₂ := b8e21
               grind)
            | exact resolve b8e4545 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4545
          have b8e4733 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e98 y x x
               have i₂ := b8e4550
               grind)
            | exact superpose b8e4550 b8e98
            | (have j0 := b8e98 y x x
               grind)
            | exact resolve b8e98 b8e4550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98 b8e4550
          have b8e4736 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b8e4733 X0
               grind)
            | (have r₁ := b8e4733 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e4733 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4733
          have b8e148267 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e309 x (σ y) x
               have i₂ := b8e4736 x
               grind)
            | exact superpose b8e4736 b8e309
            | exact resolve b8e309 b8e4736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309
          have b8e148274 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e4736 X0
               grind)
            | exact superpose b8e4736 b8e20
            | (have j1 := b8e4736 X0
               grind)
            | exact resolve b8e20 b8e4736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4736
          have b8e148324 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e148274 X0
               have i₂ := b8e4380
               grind)
            | exact superpose b8e4380 b8e148274
            | (have j0 := b8e148274 X0
               grind)
            | exact resolve b8e148274 b8e4380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148274
          have b8e148325 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e148324 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148324
          have b8e148327 : ∀ X1 : G, y = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e148267 X1
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e148267
            | exact resolve b8e148267 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148267
          have b8e148330 : ∀ X1 : G, (σ x) = (σ y) ∨ y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b8e148327 X1
               have i₂ := b8e148325 (σ x)
               grind)
            | exact superpose b8e148325 b8e148327
            | (have j0 := b8e148327 X1
               grind)
            | exact resolve b8e148327 b8e148325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148325 b8e148327
          have b8e148332 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have j0 := b8e148330 X1
               grind)
            | (have r₁ := b8e148330 X1
               have r₂ := b8e23
               grind)
            | exact resolve b8e148330 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148330
          have b8e148575 : x = y := by
            first
            | (have i₁ := b8e4380
               have i₂ := b8e148332 x
               grind)
            | exact superpose b8e148332 b8e4380
            | exact resolve b8e4380 b8e148332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4380 b8e148332
          have b8e148578 : False := by grind
          exact b8e148578

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation3591 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3591 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e21 X0 X1
           grind)
        | exact superpose b0e21 b0e12
        | exact resolve b0e12 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op (M.op X0 X2) X1)
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
           have i₂ := b0e11 X0 X1 (M.op X2 X3)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 (M.op (M.op X0 x) X1)
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e27
        | exact resolve b0e27 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) x
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have j0 := b0e36 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e38 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e35 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e56 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X2 X2
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e56 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e69 : (σ x) = (M.op x (σ x)) := by
        first
        | (have i₁ := b0e33 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e33
        | exact resolve b0e33 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e33 (M.op X0 x) X1
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 x X2 (M.op X0 X1)
           have i₂ := b0e33 X0 X1
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e22 X1 X0
           grind)
        | exact superpose b0e22 b0e12
        | exact resolve b0e12 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e148 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e26
        | exact resolve b0e26 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e165 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (M.op (M.op X0 (σ x)) X1)
           have i₂ := b0e11 X0 X1 (σ x)
           grind)
        | exact superpose b0e11 b0e28
        | exact resolve b0e28 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e170 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) X0) (M.op (M.op (σ x) X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) X1 (M.op (σ x) X0)
           have i₂ := b0e28 X0
           grind)
        | exact superpose b0e28 b0e11
        | exact resolve b0e11 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e171 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
        intro X1
        first
        | (have i₁ := b0e170 x X1
           have i₂ := b0e76 (σ x) x X1
           grind)
        | exact superpose b0e76 b0e170
        | exact resolve b0e170 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76 b0e170
      have b0e179 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e171 (σ y)
           grind)
        | exact superpose b0e171 b0e18
        | exact resolve b0e18 b0e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e206 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op x X0) X2) (M.op (M.op x X2) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29 x X2 (M.op x X0) X1
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e29
        | exact resolve b0e29 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e229 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op x X0) (σ x)) (M.op (σ x) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 x (σ x) X0 X1
           have i₂ := b0e69
           grind)
        | exact superpose b0e69 b0e29
        | exact resolve b0e29 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e232 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e29 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
           have i₂ := b0e11 X0 X1 (M.op X3 X4)
           grind)
        | exact superpose b0e11 b0e29
        | exact resolve b0e29 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e243 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op (M.op X2 x) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e75 (M.op X2 X0) (M.op (M.op X2 x) X1)
           have i₂ := b0e29 X2 x X0 X1
           grind)
        | exact superpose b0e29 b0e75
        | exact resolve b0e75 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e252 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e243 X0 X1 X2
           have i₂ := b0e75 X2 X1
           grind)
        | exact superpose b0e75 b0e243
        | exact resolve b0e243 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e243
      have b0e256 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (σ x) (M.op x (σ x))) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e229 X0 X1
           have i₂ := b0e232 (σ x) X1 X0 x (σ x)
           grind)
        | exact superpose b0e232 b0e229
        | exact resolve b0e229 b0e232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e229 b0e232
      have b0e278 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e206 X0 X1 x
           have i₂ := b0e29 x x X0 X1
           grind)
        | exact superpose b0e29 b0e206
        | exact resolve b0e206 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e206
      have b0e288 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op x (σ x)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e256 X0 X1
           have i₂ := b0e165 x (σ x)
           grind)
        | exact superpose b0e165 b0e256
        | exact resolve b0e256 b0e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e165 b0e256
      have b0e300 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e288 X0 X1
           have i₂ := b0e278 (σ x) X1
           grind)
        | exact superpose b0e278 b0e288
        | exact resolve b0e288 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e288
      have b0e308 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op x X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e300 X0 X1
           have i₂ := b0e171 X1
           grind)
        | exact superpose b0e171 b0e300
        | exact resolve b0e300 b0e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e171 b0e300
      have b0e317 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op (M.op x X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29 x X1 X0 X2
           have i₂ := b0e278 X0 X1
           grind)
        | exact superpose b0e278 b0e29
        | exact resolve b0e29 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e318 : ∀ X0 X1 : G, (M.op x X1) = (M.op X0 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X1 X0
           have i₂ := b0e278 X0 X1
           grind)
        | exact superpose b0e278 b0e11
        | exact resolve b0e11 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e342 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e317 X0 X1 X2
           have i₂ := b0e278 X1 X2
           grind)
        | exact superpose b0e278 b0e317
        | exact resolve b0e317 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e317
      have b0e404 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op x X0)) X2) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 (M.op X1 (M.op x X0)) X2
           have i₂ := b0e30 X1 X2 x X0
           grind)
        | exact superpose b0e30 b0e33
        | exact resolve b0e33 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e408 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e404 X0 X1 X2
           have i₂ := b0e308 X1 X0
           grind)
        | exact superpose b0e308 b0e404
        | exact resolve b0e404 b0e308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e404
      have b0e566 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e62 X0 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e567 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e566 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e566
      have b0e575 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e567 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e567 X0
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e567 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e567
      have b0e629 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e21 X0 (τ X0)
           have i₂ := b0e575 (τ X0)
           grind)
        | exact superpose b0e575 b0e21
        | exact resolve b0e21 b0e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e634 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e629 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e629
        | exact resolve b0e629 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e629
      have b0e639 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e634 X0
           have i₂ := b0e575 X0
           grind)
        | exact superpose b0e575 b0e634
        | exact resolve b0e634 b0e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e634
      have b0e1486 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e85 x X0
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e85
        | exact resolve b0e85 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e1513 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e1486 X0
           have i₂ := b0e38 (τ X0)
           grind)
        | exact superpose b0e38 b0e1486
        | exact resolve b0e1486 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e1486
      have b0e3215 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e575 (τ X0)
           have i₂ := b0e148 X0 X0
           grind)
        | exact superpose b0e148 b0e575
        | exact resolve b0e575 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148
      have b0e3229 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e3215 X0
           have i₂ := b0e575 X0
           grind)
        | exact superpose b0e575 b0e3215
        | exact resolve b0e3215 b0e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e575 b0e3215
      have b0e16843 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (M.op (τ (M.op x X0)) x) := by
        intro X0
        first
        | (have i₁ := b0e1513 (M.op x X0)
           have i₂ := b0e278 X0 (σ x)
           grind)
        | exact superpose b0e278 b0e1513
        | exact resolve b0e1513 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e16886 : ∀ X0 : G, (M.op (τ X0) x) = (M.op (τ (M.op x X0)) x) := by
        intro X0
        first
        | (have i₁ := b0e16843 X0
           have i₂ := b0e1513 X0
           grind)
        | exact superpose b0e1513 b0e16843
        | exact resolve b0e16843 b0e1513
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1513 b0e16843
      have b0e20471 : ∀ X0 : G, (M.op x (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e318 (τ X0) (τ X0)
           have i₂ := b0e3229 X0
           grind)
        | exact superpose b0e3229 b0e318
        | exact resolve b0e318 b0e3229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318
      have b0e41687 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op X0 X0) X1
           have i₂ := b0e342 X0 X0 X0
           grind)
        | exact superpose b0e342 b0e14
        | (have j0 := b0e14 (M.op X0 X0) X1
           grind)
        | (have r₁ := b0e14 (M.op x x) X1
           have r₂ := b0e342 x x x
           grind)
        | exact resolve b0e14 b0e342
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e342
      have b0e41751 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e41687 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41687
      have b0e75157 : ∀ X0 X1 : G, (M.op (τ (M.op x X0)) X1) = (M.op (M.op (τ X0) x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e75 (τ (M.op x X0)) X1
           have i₂ := b0e16886 X0
           grind)
        | exact superpose b0e16886 b0e75
        | exact resolve b0e75 b0e16886
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e75184 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (τ X0) x) (M.op (τ (M.op x X0)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e252 x X1 (τ (M.op x X0))
           have i₂ := b0e16886 X0
           grind)
        | exact superpose b0e16886 b0e252
        | exact resolve b0e252 b0e16886
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e252 b0e16886
      have b0e75233 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (M.op (τ X0) (M.op (τ (M.op x X0)) X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e75184 X0 X1
           have i₂ := b0e408 x (τ X0) (M.op (τ (M.op x X0)) X1)
           grind)
        | exact superpose b0e408 b0e75184
        | exact resolve b0e75184 b0e408
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75184
      have b0e75246 : ∀ X0 X1 : G, (M.op (τ (M.op x X0)) X1) = (M.op x (M.op (τ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e75157 X0 X1
           have i₂ := b0e408 x (τ X0) X1
           grind)
        | exact superpose b0e408 b0e75157
        | exact resolve b0e75157 b0e408
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e408 b0e75157
      have b0e75286 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ X0) (M.op (τ (M.op x X0)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e75233 X0 X1
           have i₂ := b0e33 (τ X0) (M.op (τ (M.op x X0)) X1)
           grind)
        | exact superpose b0e33 b0e75233
        | exact resolve b0e75233 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75233
      have b0e75299 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op x X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e75246 X0 X1
           have i₂ := b0e33 (τ X0) X1
           grind)
        | exact superpose b0e33 b0e75246
        | exact resolve b0e75246 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e75246
      have b0e96950 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (σ (M.op (τ X0) (τ (M.op x X0)))) := by
        intro X0
        first
        | (have i₁ := b0e639 (M.op x X0)
           have i₂ := b0e75299 X0 (τ (M.op x X0))
           grind)
        | exact superpose b0e75299 b0e639
        | exact resolve b0e639 b0e75299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e639
      have b0e96963 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (τ (M.op x X0)))) = (k (M.op (τ X0) (τ (M.op x X0))) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e41751 (τ (M.op x X0)) X1
           have i₂ := b0e75299 X0 (τ (M.op x X0))
           grind)
        | exact superpose b0e75299 b0e41751
        | exact resolve b0e41751 b0e75299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e97191 : ∀ X0 : G, (M.op (M.op x X0) X0) = (σ (M.op (τ X0) (τ (M.op x X0)))) := by
        intro X0
        first
        | (have i₁ := b0e96950 X0
           have i₂ := b0e308 (M.op x X0) X0
           grind)
        | exact superpose b0e308 b0e96950
        | exact resolve b0e96950 b0e308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96950
      have b0e97282 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ (M.op x X0)))) := by
        intro X0
        first
        | (have i₁ := b0e97191 X0
           have i₂ := b0e278 X0 X0
           grind)
        | exact superpose b0e278 b0e97191
        | exact resolve b0e97191 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97191
      have b0e135549 : ∀ X0 : G, (M.op x (τ (M.op x X0))) = (M.op (τ X0) (τ (M.op (M.op x X0) (M.op x X0)))) := by
        intro X0
        first
        | (have i₁ := b0e75299 X0 (τ (M.op (M.op x X0) (M.op x X0)))
           have i₂ := b0e20471 (M.op x X0)
           grind)
        | exact superpose b0e20471 b0e75299
        | exact resolve b0e75299 b0e20471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75299
      have b0e135647 : ∀ X0 : G, (M.op x (τ (M.op x X0))) = (M.op (τ X0) (τ (M.op (M.op x X0) X0))) := by
        intro X0
        first
        | (have i₁ := b0e135549 X0
           have i₂ := b0e308 (M.op x X0) X0
           grind)
        | exact superpose b0e308 b0e135549
        | exact resolve b0e135549 b0e308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135549
      have b0e135731 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op x (τ (M.op x X0))) := by
        intro X0
        first
        | (have i₁ := b0e135647 X0
           have i₂ := b0e278 X0 X0
           grind)
        | exact superpose b0e278 b0e135647
        | exact resolve b0e135647 b0e278
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e278 b0e135647
      have b0e135797 : ∀ X0 : G, (M.op x (τ X0)) = (M.op x (τ (M.op x X0))) := by
        intro X0
        first
        | (have i₁ := b0e135731 X0
           have i₂ := b0e20471 X0
           grind)
        | exact superpose b0e20471 b0e135731
        | exact resolve b0e135731 b0e20471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20471 b0e135731
      have b0e137357 : ∀ X0 X1 : G, (M.op X1 (M.op x (τ X0))) = (M.op X1 (τ (M.op x X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e308 X1 (τ (M.op x X0))
           have i₂ := b0e135797 X0
           grind)
        | exact superpose b0e135797 b0e308
        | exact resolve b0e308 b0e135797
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e137461 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op x X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e137357 X0 X1
           have i₂ := b0e308 X1 (τ X0)
           grind)
        | exact superpose b0e308 b0e137357
        | exact resolve b0e137357 b0e308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e308 b0e137357
      have b0e154933 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X1)) = (k (M.op (τ X0) (τ (M.op x X0))) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e85 (M.op (τ X0) (τ (M.op x X0))) X1
           have i₂ := b0e97282 X0
           grind)
        | exact superpose b0e97282 b0e85
        | exact resolve b0e85 b0e97282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85 b0e97282
      have b0e154947 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X1)) = (M.op (τ X1) (M.op (τ X0) (τ (M.op x X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e154933 X0 X1
           have i₂ := b0e96963 X0 (τ X1)
           grind)
        | exact superpose b0e96963 b0e154933
        | exact resolve b0e154933 b0e96963
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96963 b0e154933
      have b0e154996 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X1)) = (M.op (τ X1) (M.op (τ X0) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e154947 X0 X1
           have i₂ := b0e137461 X0 (τ X0)
           grind)
        | exact superpose b0e137461 b0e154947
        | exact resolve b0e154947 b0e137461
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137461 b0e154947
      have b0e155036 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X1)) = (M.op (τ X1) (τ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e154996 X0 X1
           have i₂ := b0e3229 X0
           grind)
        | exact superpose b0e3229 b0e154996
        | exact resolve b0e154996 b0e3229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e154996
      have b0e155069 : ∀ X0 X1 : G, (M.op (τ X1) (τ (M.op X0 X0))) = (τ (M.op X1 (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e155036 X0 X1
           have i₂ := b0e41751 X0 X1
           grind)
        | exact superpose b0e41751 b0e155036
        | exact resolve b0e155036 b0e41751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41751 b0e155036
      have b0e203298 : ∀ X0 : G, (M.op x (τ (M.op x X0))) = (M.op (τ X0) (τ (M.op (M.op x X0) (M.op x X0)))) := by
        intro X0
        first
        | (have i₁ := b0e75286 X0 (τ (M.op x X0))
           have i₂ := b0e3229 (M.op x X0)
           grind)
        | exact superpose b0e3229 b0e75286
        | exact resolve b0e75286 b0e3229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3229 b0e75286
      have b0e203513 : ∀ X0 : G, (M.op x (τ (M.op x X0))) = (τ (M.op X0 (M.op (M.op x X0) (M.op x X0)))) := by
        intro X0
        first
        | (have i₁ := b0e203298 X0
           have i₂ := b0e155069 (M.op x X0) X0
           grind)
        | exact superpose b0e155069 b0e203298
        | exact resolve b0e203298 b0e155069
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155069 b0e203298
      have b0e203604 : ∀ X0 : G, (τ (M.op x (M.op x X0))) = (M.op x (τ (M.op x X0))) := by
        intro X0
        first
        | (have i₁ := b0e203513 X0
           have i₂ := b0e11 x (M.op x X0) X0
           grind)
        | exact superpose b0e11 b0e203513
        | exact resolve b0e203513 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e203513
      have b0e203651 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x (M.op x X0))) := by
        intro X0
        first
        | (have i₁ := b0e203604 X0
           have i₂ := b0e135797 X0
           grind)
        | exact superpose b0e135797 b0e203604
        | exact resolve b0e203604 b0e135797
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135797 b0e203604
      have b0e203688 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e203651 X0
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e203651
        | exact resolve b0e203651 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e203651
      have b0e205086 : ∀ X0 : G, (M.op x X0) = (σ (M.op x (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op x X0)
           have i₂ := b0e203688 X0
           grind)
        | exact superpose b0e203688 b0e13
        | exact resolve b0e13 b0e203688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e203688
      have b0e206170 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e205086 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e205086
        | exact resolve b0e205086 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e205086
      have b0e208846 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e179
           have i₂ := b0e206170 y
           grind)
        | exact superpose b0e206170 b0e179
        | (have r₁ := b0e179
           have r₂ := b0e206170 y
           grind)
        | exact resolve b0e179 b0e206170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179 b0e206170
      have b0e208910 : False := by grind
      exact b0e208910
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e34 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e15 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) X0
             grind)
          | (have r₁ := b1e15 (σ y) x
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e42 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e35 (σ X0)
             grind)
          | exact superpose b1e35 b1e18
          | exact resolve b1e18 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e160 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e42 x
             grind)
          | exact superpose b1e42 b1e19
          | exact resolve b1e19 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e161 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e42 y
             grind)
          | exact superpose b1e42 b1e22
          | exact resolve b1e22 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e187 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e161
             grind)
          | exact superpose b1e161 b1e13
          | exact resolve b1e13 b1e161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e161
        have b1e189 : y = (k y y) := by
          first
          | (have i₁ := b1e187
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e187
          | exact resolve b1e187 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e187
        have b1e213 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e189
             grind)
          | exact superpose b1e189 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e189
        have b1e214 : y = (M.op y y) := by grind
        clear b1e213
        have b1e234 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 y X0
             have i₂ := b1e214
             grind)
          | exact superpose b1e214 b1e15
          | (have j0 := b1e15 y X0
             grind)
          | (have r₁ := b1e15 y x
             have r₂ := b1e214
             grind)
          | exact resolve b1e15 b1e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e214
        have b1e239 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b1e234 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e234
        have b1e1529 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e160
             have i₂ := b1e239 x
             grind)
          | exact superpose b1e239 b1e160
          | exact resolve b1e160 b1e239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160 b1e239
        have b1e1540 : False := by grind
        exact b1e1540
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e32 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1683 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e60 x x
             grind)
          | exact superpose b2e60 b2e21
          | (have j1 := b2e60 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e60 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e60 x x
             grind)
          | exact resolve b2e21 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e1764 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1683
        have b2e1794 : (σ x) ≠ (σ (k x x)) := by
          first
          | (have r₁ := b2e1764
             have r₂ := b2e21
             grind)
          | exact resolve b2e1764 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1764
        have b2e1832 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1794
             have i₂ := b2e33 x
             grind)
          | exact superpose b2e33 b2e1794
          | exact resolve b2e1794 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e1794
        have b2e1838 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1832
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1832
          | exact resolve b2e1832 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1832
        have b2e1839 : False := by grind
        exact b2e1839
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e34 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e42 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e35 (σ X0)
             grind)
          | exact superpose b3e35 b3e18
          | exact resolve b3e18 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e131 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e42 x
             grind)
          | exact superpose b3e42 b3e22
          | exact resolve b3e22 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e169 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e131
             grind)
          | exact superpose b3e131 b3e13
          | exact resolve b3e13 b3e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e131
        have b3e171 : x = (k x x) := by
          first
          | (have i₁ := b3e169
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e169
          | exact resolve b3e169 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e169
        have b3e189 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e171
             grind)
          | exact superpose b3e171 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e190 : x = (M.op x x) := by grind
        clear b3e189
        have b3e192 : False := by grind
        exact b3e192
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e16 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) X0
               grind)
            | (have r₁ := b4e16 (σ y) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e40 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e42 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e39 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e48 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e41 (σ X0)
               grind)
            | exact superpose b4e41 b4e19
            | exact resolve b4e19 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e49 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e48 X0
               have i₂ := b4e42 X0
               grind)
            | exact superpose b4e42 b4e48
            | exact resolve b4e48 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e48
          have b4e249 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e49 x
               grind)
            | exact resolve b4e20 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e260 : False := by grind
          exact b4e260
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e38 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e38 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1763 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e66 y y
               grind)
            | exact superpose b5e66 b5e24
            | (have j1 := b5e66 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e66 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e66 x y
               grind)
            | exact resolve b5e24 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e1842 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1763
          have b5e1872 : (σ y) ≠ (σ (k y y)) := by
            first
            | (have r₁ := b5e1842
               have r₂ := b5e24
               grind)
            | exact resolve b5e1842 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1842
          have b5e1910 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1872
               have i₂ := b5e39 y
               grind)
            | exact superpose b5e39 b5e1872
            | exact resolve b5e1872 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e1872
          have b5e1917 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1910
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1910
            | exact resolve b5e1910 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1910
          have b5e1918 : False := by grind
          exact b5e1918
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e32 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e35 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e33 (σ X0)
             grind)
          | exact superpose b6e33 b6e18
          | exact resolve b6e18 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e102 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e35 x
             grind)
          | exact superpose b6e35 b6e22
          | exact resolve b6e22 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e123 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e102
             grind)
          | exact superpose b6e102 b6e13
          | exact resolve b6e13 b6e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102
        have b6e125 : x = (k x x) := by
          first
          | (have i₁ := b6e123
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e123
          | exact resolve b6e123 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e194 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e125
             grind)
          | exact superpose b6e125 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e195 : x = (M.op x x) := by grind
        clear b6e194
        have b6e197 : False := by grind
        exact b6e197
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e42 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e42 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e45 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e43 (σ X0)
               grind)
            | exact superpose b7e43 b7e19
            | exact resolve b7e19 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e126 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e45 y
               grind)
            | exact superpose b7e45 b7e24
            | exact resolve b7e24 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e148 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e126
               grind)
            | exact superpose b7e126 b7e14
            | exact resolve b7e14 b7e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e150 : y = (k y y) := by
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
          have b7e173 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e150
               grind)
            | exact superpose b7e150 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e174 : y = (M.op y y) := by grind
          clear b7e173
          have b7e176 : False := by grind
          exact b7e176
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e73 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e73 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e104 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e79 (σ X0)
               grind)
            | exact superpose b8e79 b8e19
            | (have j1 := b8e79 (σ X0)
               grind)
            | exact resolve b8e19 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e12253 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e104 x
               grind)
            | exact superpose b8e104 b8e20
            | (have j1 := b8e104 x
               grind)
            | exact resolve b8e20 b8e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e12403 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e12253
               have r₂ := b8e23
               grind)
            | exact resolve b8e12253 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12253
          have b8e12446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e12403
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e12403
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e12403 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12403
          have b8e12458 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e12446
          have b8e12464 : y = (M.op y y) := by
            first
            | (have r₁ := b8e12458
               have r₂ := b8e21
               grind)
            | exact resolve b8e12458 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12458
          have b8e12465 : False := by grind
          exact b8e12465

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation3591 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op (M.op X0 X2) X1)
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X2 X0) ∨ (M.op X0 X0) = X0 ∨ (k (M.op X1 X2) X0) = (M.op X0 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X1 X2) X2
           have i₂ := b0e16 (M.op X1 X2) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op (M.op X0 X2) X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        grind
      have b0e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e16 (σ X1) (σ X0)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e124 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op (M.op (σ x) X0) X2) (M.op (M.op (σ x) X2) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 (σ x) X2 (M.op (σ y) X0) X1
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e35
        | exact resolve b0e35 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e126 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op (M.op (M.op x X0) X2) (M.op (M.op x X2) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 x X2 (M.op y X0) X1
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e35
        | exact resolve b0e35 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e137 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op x X0) x) (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 x x X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e140 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e35 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
           have i₂ := b0e11 X0 X1 (M.op X3 X4)
           grind)
        | exact superpose b0e11 b0e35
        | exact resolve b0e35 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op (M.op X1 X0) X0) (M.op X0 X0)) := by
        intro X0 X1
        grind
      have b0e153 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y (M.op x x)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e137 X0 X1
           have i₂ := b0e140 y X1 X0 x x
           grind)
        | exact superpose b0e140 b0e137
        | exact resolve b0e137 b0e140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137 b0e140
      have b0e163 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e126 X0 X1 x
           have i₂ := b0e35 x x X0 X1
           grind)
        | exact superpose b0e35 b0e126
        | exact resolve b0e126 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126
      have b0e164 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e124 X0 X1 x
           have i₂ := b0e35 (σ x) x X0 X1
           grind)
        | exact superpose b0e35 b0e124
        | exact resolve b0e124 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e124
      have b0e168 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e153 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e153
        | exact resolve b0e153 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e173 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e168 X0 X1
           have i₂ := b0e163 y X1
           grind)
        | exact superpose b0e163 b0e168
        | exact resolve b0e168 b0e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e168
      have b0e181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X1 X0
           have i₂ := b0e163 X0 X1
           grind)
        | exact superpose b0e163 b0e11
        | exact resolve b0e11 b0e163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e163
      have b0e349 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e181 X1 (M.op X1 X0)
           have i₂ := b0e181 X1 X0
           grind)
        | exact superpose b0e181 b0e181
        | exact resolve b0e181 b0e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e354 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e181 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e181
        | exact resolve b0e181 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e383 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e349 X0 X1
           have i₂ := b0e173 X1 X0
           grind)
        | exact superpose b0e173 b0e349
        | exact resolve b0e349 b0e173
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e173 b0e349
      have b0e789 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e383 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e383 X0 X1
           have i₂ := b0e16 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e16 b0e383
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e383 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e383
      have b0e2155 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have j0 := b0e59 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e2160 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e2155 X0 X1
           have i₂ := b0e181 X1 X0
           grind)
        | exact superpose b0e181 b0e2155
        | (have j0 := b0e2155 X0 X1
           grind)
        | exact resolve b0e2155 b0e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e181 b0e2155
      have b0e2301 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e2160 X0 X1
           have j1 := b0e789 X0 (M.op X1 X0)
           grind)
        | (have r₁ := b0e2160 X0 X1
           have r₂ := b0e789 X0 X1
           grind)
        | (have r₁ := b0e2160 y X1
           have r₂ := b0e789 y X1
           grind)
        | exact resolve b0e2160 b0e789
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e789 b0e2160
      have b0e2799 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e67 x x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e67
        | exact resolve b0e67 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e2962 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
      clear b0e2799
      have b0e5328 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e354
           grind)
        | exact superpose b0e354 b0e18
        | exact resolve b0e18 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8475 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e149 x (σ y)
           have i₂ := b0e164 x x
           grind)
        | exact superpose b0e164 b0e149
        | exact resolve b0e149 b0e164
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149 b0e164
      have b0e14813 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e2301 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e2301
        | exact resolve b0e2301 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2301
      have b0e14875 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e14813
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e14813
        | exact resolve b0e14813 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14813
      have b0e14909 : (M.op y (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e14875
           have i₂ := b0e354
           grind)
        | exact superpose b0e354 b0e14875
        | exact resolve b0e14875 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e354 b0e14875
      have b0e32850 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e8475 X1
           have i₂ := b0e62 X0 X1
           grind)
        | (have i₁ := b0e8475 X0
           have i₂ := b0e62 (M.op X0 X0) X1
           grind)
        | exact superpose b0e62 b0e8475
        | (have j1 := b0e62 X0 X1
           grind)
        | exact resolve b0e8475 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62 b0e8475
      have b0e32919 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e32850 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32850
      have b0e77363 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e2962
           have i₂ := b0e32919 x X0
           grind)
        | exact superpose b0e32919 b0e2962
        | (have j1 := b0e32919 x X0
           grind)
        | exact resolve b0e2962 b0e32919
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2962 b0e32919
      have b0e77419 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have j0 := b0e77363 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77363
      have b0e105676 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e14909
           have i₂ := b0e77419 y
           grind)
        | exact superpose b0e77419 b0e14909
        | exact resolve b0e14909 b0e77419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14909 b0e77419
      have b0e105714 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) := by grind
      clear b0e105676
      have b0e105731 : (σ x) = (σ y) := by
        first
        | (have r₁ := b0e105714
           have r₂ := b0e5328
           grind)
        | exact resolve b0e105714 b0e5328
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5328 b0e105714
      have b0e106838 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e105731
           grind)
        | exact superpose b0e105731 b0e18
        | exact resolve b0e18 b0e105731
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e106868 : y = (τ (σ x)) := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e105731
           grind)
        | exact superpose b0e105731 b0e12
        | exact resolve b0e12 b0e105731
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e106911 : x = y := by
        first
        | (have i₁ := b0e106868
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e106868
        | exact resolve b0e106868 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106868
      have b0e106921 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e106838
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e106838
        | exact resolve b0e106838 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106838
      have b0e106935 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e106921
           have i₂ := b0e105731
           grind)
        | exact superpose b0e105731 b0e106921
        | exact resolve b0e106921 b0e105731
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106921
      have b0e106940 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e106935
           have i₂ := b0e106911
           grind)
        | exact superpose b0e106911 b0e106935
        | exact resolve b0e106935 b0e106911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106911 b0e106935
      have b0e106943 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b0e106940
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e106940
        | exact resolve b0e106940 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e106940
      have b0e106945 : False := by grind
      exact b0e106945
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e87 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e28 X1 X0
             grind)
          | exact superpose b1e28 b1e13
          | exact resolve b1e13 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e356 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        clear b1e58
        have b1e2480 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e68 x x
             grind)
          | exact superpose b1e68 b1e21
          | (have j1 := b1e68 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e68 y x
             grind)
          | exact resolve b1e21 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e2585 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e2480
        have b1e3007 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e87
        have b1e3031 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e3007 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e3007
          | exact resolve b1e3007 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3007
        have b1e12612 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2585
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e2585
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e2585 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2585
        have b1e12620 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e12612
        have b1e12630 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e12620
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12620
          | exact resolve b1e12620 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12620
        have b1e12631 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e12630
        have b1e12641 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e12631
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12631
          | exact resolve b1e12631 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12631
        have b1e13992 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e356 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e356
        have b1e13994 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e13992 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13992
        have b1e14110 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b1e13994 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e13994
          | (have j0 := b1e13994 x
             grind)
          | exact resolve b1e13994 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13994
        have b1e15969 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e3031 x
             have i₂ := b1e12641
             grind)
          | exact superpose b1e12641 b1e3031
          | exact resolve b1e3031 b1e12641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3031 b1e12641
        have b1e16027 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e15969
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e15969
          | exact resolve b1e15969 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15969
        have b1e16034 : x = (k x x) := by
          first
          | (have r₁ := b1e16027
             have r₂ := b1e14110
             grind)
          | exact resolve b1e16027 b1e14110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14110 b1e16027
        have b1e16178 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e16034
             grind)
          | exact superpose b1e16034 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e16034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16034
        have b1e16189 : x = (M.op x x) := by grind
        clear b1e16178
        have b1e16209 : x = y := by
          first
          | (have i₁ := b1e16189
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16189
          | exact resolve b1e16189 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16189
        have b1e16237 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e16209
             grind)
          | exact superpose b1e16209 b1e21
          | exact resolve b1e21 b1e16209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16209
        have b1e16257 : False := by grind
        exact b1e16257
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e27 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X3 (M.op (M.op X0 X2) X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b2e55 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ y)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e80 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op (M.op (M.op x X0) X2) (M.op (M.op x X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e28 x X2 (M.op y X0) X1
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e28
          | exact resolve b2e28 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op x X0) x) (M.op y X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 x x X0 X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e96 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e28 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
             have i₂ := b2e12 X0 X1 (M.op X3 X4)
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e113 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y (M.op x x)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e89 X0 X1
             have i₂ := b2e96 y X1 X0 x x
             grind)
          | exact superpose b2e96 b2e89
          | exact resolve b2e89 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89 b2e96
        have b2e119 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e80 X0 X1 x
             have i₂ := b2e28 x x X0 X1
             grind)
          | exact superpose b2e28 b2e80
          | exact resolve b2e80 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e80
        have b2e123 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y y) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e113 X0 X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e113
          | exact resolve b2e113 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113
        have b2e124 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e123 X0 X1
             have i₂ := b2e119 y X1
             grind)
          | exact superpose b2e119 b2e123
          | exact resolve b2e123 b2e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123
        have b2e131 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X1 X0
             have i₂ := b2e119 X0 X1
             grind)
          | exact superpose b2e119 b2e12
          | exact resolve b2e12 b2e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119
        have b2e338 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e131 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e131
          | exact resolve b2e131 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e343 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e131 X1 (M.op X1 X0)
             have i₂ := b2e131 X1 X0
             grind)
          | exact superpose b2e131 b2e131
          | exact resolve b2e131 b2e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e370 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e343 X0 X1
             have i₂ := b2e124 X1 X0
             grind)
          | exact superpose b2e124 b2e343
          | exact resolve b2e343 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124 b2e343
        have b2e489 : (M.op y y) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b2e131 x y
             have i₂ := b2e338
             grind)
          | exact superpose b2e338 b2e131
          | exact resolve b2e131 b2e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338
        have b2e497 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b2e489
             have i₂ := b2e27 x
             grind)
          | exact superpose b2e27 b2e489
          | exact resolve b2e489 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e489
        have b2e500 : y = (M.op y y) := by
          first
          | (have i₁ := b2e497
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e497
          | exact resolve b2e497 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e497
        have b2e597 : y = (k y y) := by grind
        clear b2e500
        have b2e608 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e48 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e609 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e608
             have r₂ := b2e22
             grind)
          | exact resolve b2e608 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e608
        have b2e610 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e609
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e609
          | exact resolve b2e609 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e609
        have b2e611 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e610
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e610
          | exact resolve b2e610 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e610
        have b2e625 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 (σ y) X0 (σ x)
             have i₂ := b2e611
             grind)
          | exact superpose b2e611 b2e12
          | exact resolve b2e12 b2e611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e611
        have b2e626 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e625 X0
             have i₂ := b2e131 (σ x) X0
             grind)
          | exact superpose b2e131 b2e625
          | exact resolve b2e625 b2e131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131 b2e625
        have b2e944 : (σ y) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e626 (σ y)
             grind)
          | exact superpose b2e626 b2e22
          | exact resolve b2e22 b2e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1396 : ∀ X0 : G, (σ y) = (M.op y (σ y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e370 X0 X0
             have i₂ := b2e59 X0
             grind)
          | exact superpose b2e59 b2e370
          | (have j1 := b2e59 X0
             grind)
          | exact resolve b2e370 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e370
        have b2e1429 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b2e1396 X0
             grind)
          | (have r₁ := b2e1396 X0
             have r₂ := b2e944
             grind)
          | exact resolve b2e1396 b2e944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1396
        have b2e1433 : ∀ X0 : G, (M.op y X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e1429 X0
             have i₂ := b2e626 X0
             grind)
          | exact superpose b2e626 b2e1429
          | exact resolve b2e1429 b2e626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626 b2e1429
        have b2e1459 : ∀ X0 : G, (σ (k X0 y)) = (M.op y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e1433 (σ X0)
             grind)
          | exact superpose b2e1433 b2e18
          | exact resolve b2e18 b2e1433
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1433
        have b2e2632 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e1459 y
             have i₂ := b2e597
             grind)
          | exact superpose b2e597 b2e1459
          | exact resolve b2e1459 b2e597
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e597 b2e1459
        have b2e2654 : False := by grind
        exact b2e2654
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e35 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 X3 (M.op (M.op X0 X2) X1)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e35 (M.op (M.op X0 y) X1)
             have i₂ := b3e12 X0 X1 y
             grind)
          | exact superpose b3e12 b3e35
          | exact resolve b3e35 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e49 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e41 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e41
          | exact resolve b3e41 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e41 (M.op X0 y) X1
             grind)
          | exact superpose b3e41 b3e12
          | exact resolve b3e12 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e17 (σ X1) (σ X0)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e151 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op (M.op (σ x) X0) X2) (M.op (M.op (σ x) X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e37 (σ x) X2 (M.op (σ y) X0) X1
             have i₂ := b3e36 X0
             grind)
          | exact superpose b3e36 b3e37
          | exact resolve b3e37 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e213 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e151 X0 X1 x
             have i₂ := b3e37 (σ x) x X0 X1
             grind)
          | exact superpose b3e37 b3e151
          | exact resolve b3e151 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e151
        have b3e2358 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e75 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e75
          | exact resolve b3e75 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e2524 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e2358
        have b3e3288 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e53 (σ y) X0
             have i₂ := b3e213 y X0
             grind)
          | exact superpose b3e213 b3e53
          | exact resolve b3e53 b3e213
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e213
        have b3e4995 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e2524
             grind)
          | exact superpose b3e2524 b3e13
          | exact resolve b3e13 b3e2524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5015 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4995
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4995
          | exact resolve b3e4995 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4995
        have b3e5330 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e5015
             grind)
          | exact superpose b3e5015 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e5015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5015
        have b3e5338 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e5330
        have b3e5346 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e5338
             have r₂ := b3e20
             grind)
          | exact resolve b3e5338 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5338
        have b3e7901 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e5346
        have b3e8138 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2524
             have i₂ := b3e7901
             grind)
          | exact superpose b3e7901 b3e2524
          | exact resolve b3e2524 b3e7901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2524 b3e7901
        have b3e8149 : (σ x) = (σ y) := by grind
        clear b3e8138
        have b3e8291 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e8149
             grind)
          | exact superpose b3e8149 b3e19
          | exact resolve b3e19 b3e8149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e8298 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e8149
             grind)
          | exact superpose b3e8149 b3e13
          | exact resolve b3e13 b3e8149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8149
        have b3e8334 : x = y := by
          first
          | (have i₁ := b3e8298
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e8298
          | exact resolve b3e8298 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8298
        have b3e8336 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
          first
          | (have i₁ := b3e8291
             have i₂ := b3e3288 (σ y)
             grind)
          | exact superpose b3e3288 b3e8291
          | exact resolve b3e8291 b3e3288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3288 b3e8291
        have b3e8345 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e8336
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e8336
          | exact resolve b3e8336 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e8336
        have b3e8353 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e8345
             have i₂ := b3e8334
             grind)
          | exact superpose b3e8334 b3e8345
          | exact resolve b3e8345 b3e8334
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8334 b3e8345
        have b3e8355 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e8353
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e8353
          | exact resolve b3e8353 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8353
        have b3e8356 : False := by grind
        exact b3e8356
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e37 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X3 (M.op (M.op X0 X2) X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
               have i₂ := b4e13 X0 X1 (M.op X2 X3)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 (M.op (M.op X0 y) X1)
               have i₂ := b4e13 X0 X1 y
               grind)
            | exact superpose b4e13 b4e37
            | exact resolve b4e37 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e43 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e43
            | exact resolve b4e43 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 y X2 (M.op X0 X1)
               have i₂ := b4e43 X0 X1
               grind)
            | exact superpose b4e43 b4e13
            | exact resolve b4e13 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b4e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
          have b4e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e30 X1 X0
               grind)
            | exact superpose b4e30 b4e14
            | exact resolve b4e14 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e136 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 (M.op (M.op X0 (σ y)) X1)
               have i₂ := b4e13 X0 X1 (σ y)
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e141 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) (M.op (M.op (σ y) X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X1 (M.op (σ y) X0)
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e142 : ∀ X1 : G, (M.op y X1) = (M.op (σ y) X1) := by
            intro X1
            first
            | (have i₁ := b4e141 x X1
               have i₂ := b4e57 (σ y) x X1
               grind)
            | exact superpose b4e57 b4e141
            | exact resolve b4e141 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57 b4e141
          have b4e187 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op (M.op (M.op y X0) X2) (M.op (M.op y X2) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e39 y X2 (M.op y X0) X1
               have i₂ := b4e37 X0
               grind)
            | exact superpose b4e37 b4e39
            | exact resolve b4e39 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e209 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op y X0) (σ y)) (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 y (σ y) X0 X1
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e39
            | exact resolve b4e39 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e212 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e39 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
               have i₂ := b4e13 X0 X1 (M.op X3 X4)
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e236 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (σ y) (M.op y (σ y))) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e209 X0 X1
               have i₂ := b4e212 (σ y) X1 X0 y (σ y)
               grind)
            | exact superpose b4e212 b4e209
            | exact resolve b4e209 b4e212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209 b4e212
          have b4e252 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e187 X0 X1 x
               have i₂ := b4e39 y x X0 X1
               grind)
            | exact superpose b4e39 b4e187
            | exact resolve b4e187 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e187
          have b4e258 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y (σ y)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e236 X0 X1
               have i₂ := b4e136 y (σ y)
               grind)
            | exact superpose b4e136 b4e236
            | exact resolve b4e236 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136 b4e236
          have b4e268 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e258 X0 X1
               have i₂ := b4e252 (σ y) X1
               grind)
            | exact superpose b4e252 b4e258
            | exact resolve b4e258 b4e252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e258
          have b4e274 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e268 X0 X1
               have i₂ := b4e142 X1
               grind)
            | exact superpose b4e142 b4e268
            | exact resolve b4e268 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142 b4e268
          have b4e356 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 (M.op y X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e43 (M.op X1 (M.op y X0)) X2
               have i₂ := b4e40 X1 X2 y X0
               grind)
            | exact superpose b4e40 b4e43
            | exact resolve b4e43 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e43
          have b4e358 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e356 X0 X1 X2
               have i₂ := b4e274 X1 X0
               grind)
            | exact superpose b4e274 b4e356
            | exact resolve b4e356 b4e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e356
          have b4e524 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X1 X0
               have i₂ := b4e252 X0 X1
               grind)
            | exact superpose b4e252 b4e13
            | exact resolve b4e13 b4e252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e252
          have b4e2691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e77 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e2692 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e2691 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2691
          have b4e6815 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 (M.op X1 X0)))) := by
            intro X0 X1
            grind
          have b4e6832 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X1 X0) X3 X2
               have i₂ := b4e358 X0 X1 X2
               grind)
            | exact superpose b4e358 b4e13
            | exact resolve b4e13 b4e358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6889 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op X2 (M.op (M.op X1 X2) (M.op X0 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e6832 X0 X1 X2 X3
               have i₂ := b4e358 (M.op X1 X2) X0 X3
               grind)
            | exact superpose b4e358 b4e6832
            | exact resolve b4e6832 b4e358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e358 b4e6832
          have b4e6903 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e6815 X0 X1
               have i₂ := b4e524 X1 X0
               grind)
            | exact superpose b4e524 b4e6815
            | exact resolve b4e6815 b4e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6815
          have b4e6996 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X0 X3)) = (M.op (M.op X1 X0) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e6889 X0 X1 x X3
               have i₂ := b4e13 X1 (M.op X0 X3) x
               grind)
            | exact superpose b4e13 b4e6889
            | exact resolve b4e6889 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6889
          have b4e7010 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6903 X0 X1
               have i₂ := b4e274 X0 X0
               grind)
            | exact superpose b4e274 b4e6903
            | exact resolve b4e6903 b4e274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e274 b4e6903
          have b4e12168 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e7010 X1 X1
               have i₂ := b4e72 X0 X1
               grind)
            | (have i₁ := b4e7010 X0 X1
               have i₂ := b4e72 (M.op X1 X0) X1
               grind)
            | exact superpose b4e72 b4e7010
            | (have j1 := b4e72 X0 X1
               grind)
            | exact resolve b4e7010 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e12256 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e12168 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12168
          have b4e12381 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e2692 (M.op X0 X0)
               have i₂ := b4e7010 X0 X0
               grind)
            | exact superpose b4e7010 b4e2692
            | (have j0 := b4e2692 (M.op X0 X0)
               grind)
            | exact resolve b4e2692 b4e7010
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7010
          have b4e12387 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e2692 (τ X0)
               have i₂ := b4e30 X0 (τ X0)
               grind)
            | exact superpose b4e30 b4e2692
            | (have j0 := b4e2692 (τ X0)
               grind)
            | exact resolve b4e2692 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e2692
          have b4e12390 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b4e12381 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12381
          have b4e12408 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e12387 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e12387
            | (have j0 := b4e12387 X0
               grind)
            | exact resolve b4e12387 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12387
          have b4e12419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e12408 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e12408
            | (have j0 := b4e12408 X0
               grind)
            | exact resolve b4e12408 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12408
          have b4e38375 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e18 X0 X0
               have i₂ := b4e12256 X0 X1
               grind)
            | exact superpose b4e12256 b4e18
            | (have j0 := b4e18 X0 X0
               have j1 := b4e12256 X0 X1
               grind)
            | exact resolve b4e18 b4e12256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38392 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e92 X0 (σ X0)
               have i₂ := b4e12256 (σ X0) X1
               grind)
            | exact superpose b4e12256 b4e92
            | (have j1 := b4e12256 (σ X0) X1
               grind)
            | exact resolve b4e92 b4e12256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e38438 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e29 X1 X0
               have i₂ := b4e12256 X0 (τ X1)
               grind)
            | exact superpose b4e12256 b4e29
            | (have j1 := b4e12256 X0 X1
               grind)
            | exact resolve b4e29 b4e12256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e12256
          have b4e38454 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e38375 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38375
          have b4e38484 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38392 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e38392
            | (have j0 := b4e38392 X0 X1
               grind)
            | exact resolve b4e38392 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38392
          have b4e65593 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6996 (σ (M.op X0 X0)) (σ (M.op X0 X0)) X1
               have i₂ := b4e12390 X0
               grind)
            | exact superpose b4e12390 b4e6996
            | exact resolve b4e6996 b4e12390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12390
          have b4e65610 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e65593 X0 X1
               have i₂ := b4e524 (σ (M.op X0 X0)) X1
               grind)
            | exact superpose b4e524 b4e65593
            | exact resolve b4e65593 b4e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65593
          have b4e185950 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38454 X0 X0
               have i₂ := b4e38484 X0 X1
               grind)
            | exact superpose b4e38484 b4e38454
            | (have j0 := b4e38454 X0 X1
               have j1 := b4e38484 X0 X1
               grind)
            | exact resolve b4e38454 b4e38484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38454 b4e38484
          have b4e186004 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e185950 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185950
          have b4e222537 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e186004 X0 (σ X1)
               grind)
            | exact superpose b4e186004 b4e19
            | (have j1 := b4e186004 X0 X1
               grind)
            | exact resolve b4e19 b4e186004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186004
          have b4e647659 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e38438 X1 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e38438
            | (have j0 := b4e38438 X1 X1
               grind)
            | exact resolve b4e38438 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38438
          have b4e647679 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e647659 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e647659
            | (have j0 := b4e647659 X0 X1
               grind)
            | exact resolve b4e647659 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e647659
          have b4e654794 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e12419 X0
               have i₂ := b4e647679 X1 X0
               grind)
            | exact superpose b4e647679 b4e12419
            | (have j0 := b4e12419 X0
               have j1 := b4e647679 X1 X0
               grind)
            | (have r₁ := b4e12419 X1
               have r₂ := b4e647679 X0 X1
               grind)
            | exact resolve b4e12419 b4e647679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12419 b4e647679
          have b4e654797 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e654794 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e654794
          have b4e1016502 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e222537 x y
               grind)
            | exact superpose b4e222537 b4e20
            | (have j1 := b4e222537 x x
               grind)
            | exact resolve b4e20 b4e222537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222537
          have b4e1016584 : x = (M.op x x) := by
            first
            | (have j1 := b4e654797 x x
               grind)
            | (have r₁ := b4e1016502
               have r₂ := b4e654797 x y
               grind)
            | exact resolve b4e1016502 b4e654797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e654797 b4e1016502
          have b4e1025830 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e65610 x X0
               have i₂ := b4e1016584
               grind)
            | exact superpose b4e1016584 b4e65610
            | exact resolve b4e65610 b4e1016584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65610
          have b4e1025959 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e6996 x x X0
               have i₂ := b4e1016584
               grind)
            | exact superpose b4e1016584 b4e6996
            | exact resolve b4e6996 b4e1016584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6996 b4e1016584
          have b4e1026003 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e1025959 X0
               have i₂ := b4e524 x X0
               grind)
            | exact superpose b4e524 b4e1025959
            | exact resolve b4e1025959 b4e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e524 b4e1025959
          have b4e1150588 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1025830 (σ y)
               grind)
            | exact superpose b4e1025830 b4e20
            | exact resolve b4e20 b4e1025830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1025830
          have b4e1150967 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e1150588
               have i₂ := b4e52
               grind)
            | exact superpose b4e52 b4e1150588
            | exact resolve b4e1150588 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e1150588
          have b4e1151062 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e1150967
               have i₂ := b4e1026003 y
               grind)
            | exact superpose b4e1026003 b4e1150967
            | exact resolve b4e1150967 b4e1026003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1026003 b4e1150967
          have b4e1151103 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e1151062
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1151062
            | exact resolve b4e1151062 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1151062
          have b4e1151104 : False := by grind
          exact b4e1151104
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : y = (k y y) := by grind
          have b5e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
          have b5e2189 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e71 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e2190 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e2189 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2189
          have b5e11015 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e2190 y
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e2190
            | (have j0 := b5e2190 y
               grind)
            | exact resolve b5e2190 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e2190
          have b5e11019 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e11015
          have b5e11037 : False := by grind
          exact b5e11037
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
          intro X0 X1 X2
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
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) X0 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 X3 (M.op (M.op X0 X2) X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e30 X1 X0
             grind)
          | exact superpose b6e30 b6e13
          | exact resolve b6e13 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e83 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e87 : x = (M.op y x) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e20
             grind)
          | exact resolve b6e83 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e90 : x = (M.op y x) := by
          first
          | (have r₁ := b6e87
             have r₂ := b6e21
             grind)
          | exact resolve b6e87 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e92 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 x
             have i₂ := b6e90
             grind)
          | exact superpose b6e90 b6e12
          | exact resolve b6e12 b6e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e109 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op (M.op (σ x) X0) X2) (M.op (M.op (σ x) X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e41 (σ x) X2 (M.op (σ y) X0) X1
             have i₂ := b6e40 X0
             grind)
          | exact superpose b6e40 b6e41
          | exact resolve b6e41 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e119 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (σ x) X0) (σ x)) (M.op (σ y) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e41 (σ x) (σ x) X0 X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e41
          | exact resolve b6e41 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e123 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e41 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
             have i₂ := b6e12 X0 X1 (M.op X3 X4)
             grind)
          | exact superpose b6e12 b6e41
          | exact resolve b6e41 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e137 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ x))) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e119 X0 X1
             have i₂ := b6e123 (σ y) X1 X0 (σ x) (σ x)
             grind)
          | exact superpose b6e123 b6e119
          | exact resolve b6e119 b6e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e119 b6e123
        have b6e145 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e109 X0 X1 x
             have i₂ := b6e41 (σ x) x X0 X1
             grind)
          | exact superpose b6e41 b6e109
          | exact resolve b6e109 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e109
        have b6e150 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e137 X0 X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e137
          | exact resolve b6e137 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e137
        have b6e153 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ y) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e150 X0 X1
             have i₂ := b6e145 (σ y) X1
             grind)
          | exact superpose b6e145 b6e150
          | exact resolve b6e150 b6e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150
        have b6e230 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b6e48
        have b6e243 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e230 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e230
          | exact resolve b6e230 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e230
        have b6e295 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (σ y) X1 X0
             have i₂ := b6e145 X0 X1
             grind)
          | exact superpose b6e145 b6e12
          | exact resolve b6e12 b6e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e835 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (σ y) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e295 X1 (M.op X1 X0)
             have i₂ := b6e295 X1 X0
             grind)
          | exact superpose b6e295 b6e295
          | exact resolve b6e295 b6e295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e868 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e92 X0
             have i₂ := b6e295 x X0
             grind)
          | exact superpose b6e295 b6e92
          | exact resolve b6e92 b6e295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92 b6e295
        have b6e896 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e835 X0 X1
             have i₂ := b6e868 (M.op X1 X0)
             grind)
          | exact superpose b6e868 b6e835
          | exact resolve b6e835 b6e868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e835
        have b6e909 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e896 X0 X1
             have i₂ := b6e153 X1 X0
             grind)
          | exact superpose b6e153 b6e896
          | exact resolve b6e896 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153 b6e896
        have b6e1205 : y = (k y (τ (M.op y (σ y)))) := by
          first
          | (have i₁ := b6e243 y
             have i₂ := b6e868 (σ y)
             grind)
          | exact superpose b6e868 b6e243
          | exact resolve b6e243 b6e868
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e243 b6e868
        have b6e1630 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b6e909 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e909
          | exact resolve b6e909 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e909
        have b6e3162 : y = (k y (τ (σ y))) := by
          first
          | (have i₁ := b6e1205
             have i₂ := b6e1630
             grind)
          | exact superpose b6e1630 b6e1205
          | exact resolve b6e1205 b6e1630
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1205 b6e1630
        have b6e3168 : y = (k y y) := by
          first
          | (have i₁ := b6e3162
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3162
          | exact resolve b6e3162 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3162
        have b6e3497 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e3168
             grind)
          | exact superpose b6e3168 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e3168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3168
        have b6e3506 : y = (M.op y y) := by grind
        clear b6e3497
        have b6e3517 : False := by grind
        exact b6e3517
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e75 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e78 : y = (M.op y y) := by grind
          clear b7e75
          have b7e82 : False := by grind
          exact b7e82
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b8e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op (M.op X0 X2) X1)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
               have i₂ := b8e13 X0 X1 (M.op X2 X3)
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          have b8e55 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b8e59 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
          have b8e63 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e59 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e34
            | exact resolve b8e34 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e87 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e28 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
               have i₂ := b8e13 X0 X1 (M.op X3 X4)
               grind)
            | exact superpose b8e13 b8e28
            | exact resolve b8e28 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e97 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
               have i₂ := b8e28 X2 X3 X0 X1
               grind)
            | exact superpose b8e28 b8e13
            | exact resolve b8e13 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e134 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e29 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
               have i₂ := b8e28 X2 X3 X0 X1
               grind)
            | exact superpose b8e28 b8e29
            | exact resolve b8e29 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e141 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e28 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
               have i₂ := b8e29 X1 X2 X3 X0
               grind)
            | exact superpose b8e29 b8e28
            | exact resolve b8e28 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e143 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e28 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
               have i₂ := b8e29 X1 X2 (M.op X4 X5) X0
               grind)
            | exact superpose b8e29 b8e28
            | exact resolve b8e28 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e147 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e143 X0 X1 X2 X3 X4 X5
               have i₂ := b8e87 X0 (M.op X1 X2) X3 X4 X5
               grind)
            | exact superpose b8e87 b8e143
            | exact resolve b8e143 b8e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e149 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e141 X0 X1 X2 X3 X4 x
               have i₂ := b8e97 X3 x X0 (M.op X1 X2) X4
               grind)
            | exact superpose b8e97 b8e141
            | exact resolve b8e141 b8e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e381 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e52 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e382 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e381
               have r₂ := b8e24
               grind)
            | exact resolve b8e381 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e381
          have b8e383 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e382
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e382
            | exact resolve b8e382 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e382
          have b8e386 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ (k x y)) X1) (M.op (M.op (σ y) X1) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e28 (σ y) X1 (σ x) X0
               have i₂ := b8e383
               grind)
            | exact superpose b8e383 b8e28
            | exact resolve b8e28 b8e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e383
          have b8e388 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op X1 (M.op (M.op (M.op (σ (k x y)) (σ y)) X1) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e386 X0 X1
               have i₂ := b8e134 (σ y) X1 (σ (k x y)) X1 X0
               grind)
            | exact superpose b8e134 b8e386
            | exact resolve b8e386 b8e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e386
          have b8e390 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (k x y)) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b8e388 X0 x
               have i₂ := b8e13 (M.op (σ (k x y)) (σ y)) X0 x
               grind)
            | exact superpose b8e13 b8e388
            | exact resolve b8e388 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e388
          have b8e561 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (σ (k x y)) (σ y)) X1) X0) (M.op (M.op (σ x) X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 (M.op (σ (k x y)) (σ y)) X0 X1 X2
               have i₂ := b8e390 X0
               grind)
            | exact superpose b8e390 b8e28
            | exact resolve b8e28 b8e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e573 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (σ (k x y)) (σ y)) (σ x)) X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b8e561 x X1 X2
               have i₂ := b8e97 (σ x) x (M.op (σ (k x y)) (σ y)) X1 X2
               grind)
            | exact superpose b8e97 b8e561
            | exact resolve b8e561 b8e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e561
          have b8e598 : ∀ X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op (σ x) (σ x)) X1) X2) := by
            intro X1 X2
            first
            | (have i₁ := b8e573 X1 X2
               have i₂ := b8e390 (σ x)
               grind)
            | exact superpose b8e390 b8e573
            | exact resolve b8e573 b8e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e390 b8e573
          have b8e721 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op (M.op (M.op (σ x) (σ x)) X2) X0) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 (M.op (σ x) (σ x)) X0 X2 X1
               have i₂ := b8e598 X0 X1
               grind)
            | exact superpose b8e598 b8e28
            | exact resolve b8e28 b8e598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e722 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ x)) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 (M.op (σ x) (σ x)) X1 X0 X2
               have i₂ := b8e598 X0 X1
               grind)
            | exact superpose b8e598 b8e28
            | exact resolve b8e28 b8e598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e738 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X2) X1) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e28 (M.op (M.op (σ x) (σ x)) X0) X1 X2 X3
               have i₂ := b8e598 X0 X1
               grind)
            | exact superpose b8e598 b8e28
            | exact resolve b8e28 b8e598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e739 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X1) X3) (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e28 (M.op (M.op (σ x) (σ x)) X0) X3 X1 X2
               have i₂ := b8e598 X0 X1
               grind)
            | exact superpose b8e598 b8e28
            | exact resolve b8e28 b8e598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e752 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X0)) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e739 X0 X1 X2 x
               have i₂ := b8e97 (M.op (M.op (σ x) (σ x)) X0) x X0 X1 X2
               grind)
            | exact superpose b8e97 b8e739
            | exact resolve b8e739 b8e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e739
          have b8e753 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X0) X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e738 X0 x X2 X3
               have i₂ := b8e97 X0 x (M.op (M.op (σ x) (σ x)) X0) X2 X3
               grind)
            | exact superpose b8e97 b8e738
            | exact resolve b8e738 b8e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97 b8e738
          have b8e759 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X0 (M.op (σ x) (σ x))) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e722 X0 X1 X2
               have i₂ := b8e134 (M.op (σ x) (σ x)) X1 X0 X1 X2
               grind)
            | exact superpose b8e134 b8e722
            | exact resolve b8e722 b8e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134 b8e722
          have b8e760 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X0)) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e721 X0 X1 X2
               have i₂ := b8e87 X0 X1 X2 (M.op (σ x) (σ x)) X0
               grind)
            | exact superpose b8e87 b8e721
            | exact resolve b8e721 b8e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87 b8e721
          have b8e774 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e752 X0 X1 X2
               have i₂ := b8e149 X0 X0 X1 (M.op (σ x) (σ x)) X2
               grind)
            | (have i₁ := b8e752 X0 (M.op X1 X2) x
               have i₂ := b8e149 X0 X1 X2 (M.op (M.op (σ x) (σ x)) X0) x
               grind)
            | exact superpose b8e149 b8e752
            | exact resolve b8e752 b8e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e752
          have b8e775 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X0) X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e753 X0 X2 X3
               have i₂ := b8e598 X0 X0
               grind)
            | (have i₁ := b8e753 X2 X2 X3
               have i₂ := b8e598 (M.op (M.op (σ x) (σ x)) X2) X2
               grind)
            | exact superpose b8e598 b8e753
            | exact resolve b8e753 b8e598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e598 b8e753
          have b8e779 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op X0 (M.op (σ x) (σ x))) X2) := by
            intro X0 X2
            first
            | (have i₁ := b8e759 X0 x X2
               have i₂ := b8e13 (M.op X0 (M.op (σ x) (σ x))) X2 x
               grind)
            | exact superpose b8e13 b8e759
            | exact resolve b8e759 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e759
          have b8e780 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e760 X0 X1 X2
               have i₂ := b8e147 X0 X0 X1 X2 (σ x) (σ x)
               grind)
            | (have i₁ := b8e760 x (M.op X1 X2) x
               have i₂ := b8e147 x X1 X2 x (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b8e147 b8e760
            | exact resolve b8e760 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e760
          have b8e785 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op X0 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e774 X0 X1 X2
               have i₂ := b8e149 (σ x) X0 (M.op X0 X1) (σ x) X2
               grind)
            | (have i₁ := b8e774 X1 X2 x
               have i₂ := b8e149 X1 X1 X2 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b8e149 b8e774
            | exact resolve b8e774 b8e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e149 b8e774
          have b8e787 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e780 X0 X1 X2
               have i₂ := b8e779 X0 (M.op X0 X1)
               grind)
            | exact superpose b8e779 b8e780
            | exact resolve b8e780 b8e779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e779 b8e780
          have b8e788 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e785 X0 X1 X2
               have i₂ := b8e775 (σ x) (M.op X0 (M.op X0 X1)) X2
               grind)
            | (have i₁ := b8e785 X0 X1 x
               have i₂ := b8e775 X0 (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op X0 X1))) x
               grind)
            | exact superpose b8e775 b8e785
            | exact resolve b8e785 b8e775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e785
          have b8e1004 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X2 X2) X1 X0
               have i₂ := b8e775 X2 X0 X1
               grind)
            | exact superpose b8e775 b8e13
            | exact resolve b8e13 b8e775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1081 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op X2 (M.op X3 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e787 X3 (M.op (M.op X0 X3) X1) X2
               have i₂ := b8e13 X0 X1 X3
               grind)
            | exact superpose b8e13 b8e787
            | exact resolve b8e787 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1082 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 (M.op X4 X0)) X2)) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e787 X4 (M.op (M.op X1 (M.op X4 X0)) X2) X3
               have i₂ := b8e29 X1 X2 X4 X0
               grind)
            | exact superpose b8e29 b8e787
            | exact resolve b8e787 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1122 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op (M.op (M.op X3 X3) X0) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e787 X1 X2 (M.op (M.op X3 X3) X0)
               have i₂ := b8e775 X3 X0 (M.op X1 (M.op X1 X2))
               grind)
            | exact superpose b8e775 b8e787
            | exact resolve b8e787 b8e775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1125 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 (M.op (M.op X2 X0) X1) X0
               have i₂ := b8e787 (M.op X2 X0) X1 X0
               grind)
            | exact superpose b8e787 b8e13
            | exact resolve b8e13 b8e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X0 X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e29 X0 X3 X2 (M.op X2 X1)
               have i₂ := b8e787 X2 X1 X0
               grind)
            | exact superpose b8e787 b8e29
            | exact resolve b8e29 b8e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1128 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X2 (M.op (M.op X2 (M.op X0 X3)) X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e29 X2 (M.op (M.op X2 (M.op X0 X3)) X1) X0 X3
               have i₂ := b8e787 (M.op X2 (M.op X0 X3)) X1 X0
               grind)
            | exact superpose b8e787 b8e29
            | exact resolve b8e29 b8e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1147 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e28 X0 X2 X1 (M.op (M.op X0 X2) X3)
               have i₂ := b8e787 (M.op X0 X2) X3 (M.op (M.op X0 X1) X2)
               grind)
            | exact superpose b8e787 b8e28
            | exact resolve b8e28 b8e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1182 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op (M.op X3 X0) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1122 X0 X1 X2 X3
               have i₂ := b8e1147 X3 X3 X0 X2
               grind)
            | exact superpose b8e1147 b8e1122
            | exact resolve b8e1122 b8e1147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1122
          have b8e1208 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op X0 (M.op X3 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1182 X0 X1 X2 X3
               have i₂ := b8e1081 X3 X2 X3 X0
               grind)
            | (have i₁ := b8e1182 X0 X1 (M.op X0 X1) X2
               have i₂ := b8e1081 X0 X1 X2 (M.op X2 X0)
               grind)
            | exact superpose b8e1081 b8e1182
            | exact resolve b8e1182 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1182
          have b8e1224 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op X3 (M.op X0 (M.op X3 X2))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e1208 X0 x X2 X3
               have i₂ := b8e787 x X2 X0
               grind)
            | exact superpose b8e787 b8e1208
            | exact resolve b8e1208 b8e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1208
          have b8e1833 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e28 X2 X1 (M.op X2 X0) X3
               have i₂ := b8e788 X2 X0 X1
               grind)
            | exact superpose b8e788 b8e28
            | exact resolve b8e28 b8e788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1836 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e29 X2 X1 X2 X0
               have i₂ := b8e788 X2 X0 X1
               grind)
            | exact superpose b8e788 b8e29
            | exact resolve b8e29 b8e788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e1864 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 X3 (M.op X2 (M.op X2 X0))
               have i₂ := b8e788 X2 X0 (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3)
               grind)
            | exact superpose b8e788 b8e13
            | exact resolve b8e13 b8e788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e788
          have b8e1873 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X2 (M.op (M.op X2 X0) (M.op X1 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1864 X0 X1 X2 X3
               have i₂ := b8e1082 (M.op X2 X0) X1 X3 X0 X2
               grind)
            | (have i₁ := b8e1864 X3 X1 X2 (M.op X0 (M.op X1 X2))
               have i₂ := b8e1082 X0 X1 X2 X3 (M.op X1 (M.op X2 (M.op X2 X3)))
               grind)
            | exact superpose b8e1082 b8e1864
            | exact resolve b8e1864 b8e1082
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1082 b8e1864
          have b8e1900 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1833 X0 X1 X2 X3
               have i₂ := b8e1081 X2 X3 (M.op X0 X1) X1
               grind)
            | (have i₁ := b8e1833 X0 X1 X2 (M.op X0 X1)
               have i₂ := b8e1081 X0 X1 (M.op X0 X1) (M.op X2 X1)
               grind)
            | exact superpose b8e1081 b8e1833
            | exact resolve b8e1833 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1833
          have b8e1937 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X2 (M.op X0 (M.op X2 (M.op X1 X3))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1873 X0 X1 X2 X3
               have i₂ := b8e1081 X2 (M.op X1 X3) X2 X0
               grind)
            | (have i₁ := b8e1873 X0 X0 X2 X1
               have i₂ := b8e1081 X0 X1 X2 (M.op X2 X0)
               grind)
            | exact superpose b8e1081 b8e1873
            | exact resolve b8e1873 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1873
          have b8e1960 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e1900 X0 X1 X2 X3
               have i₂ := b8e1836 X1 (M.op X2 X3) (M.op X0 X1)
               grind)
            | (have i₁ := b8e1900 X0 X1 X2 X3
               have i₂ := b8e1836 (M.op X0 X1) (M.op X2 X3) X1
               grind)
            | exact superpose b8e1836 b8e1900
            | exact resolve b8e1900 b8e1836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1900
          have b8e1988 : ∀ X1 X2 X3 : G, (M.op X1 X3) = (M.op X2 (M.op X2 (M.op X1 X3))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e1937 x X1 X2 X3
               have i₂ := b8e1224 X2 (M.op X2 (M.op X1 X3)) x
               grind)
            | exact superpose b8e1224 b8e1937
            | exact resolve b8e1937 b8e1224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1937
          have b8e1998 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op X2 X0) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e1960 X0 x X2 X3
               have i₂ := b8e13 X0 (M.op X2 X3) x
               grind)
            | exact superpose b8e13 b8e1960
            | exact resolve b8e1960 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1960
          have b8e2204 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e61 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e2205 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e2204 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2204
          have b8e2377 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1004 X0 X1 x
               have i₂ := b8e1004 X2 X1 x
               grind)
            | exact superpose b8e1004 b8e1004
            | exact resolve b8e1004 b8e1004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2436 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X2 X2) ∨ (k X2 (M.op X1 X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X2 (M.op X1 X1)
               have i₂ := b8e1004 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b8e1004 b8e17
            | (have j0 := b8e17 X1 (M.op X2 X2)
               grind)
            | exact resolve b8e17 b8e1004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2439 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
            intro X0 X1
            grind
          have b8e2492 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b8e2439 x X1
               have i₂ := b8e1988 X1 x X1
               grind)
            | (have i₁ := b8e2439 X1 X1
               have i₂ := b8e1988 X1 x (M.op X1 (M.op X1 X1))
               grind)
            | exact superpose b8e1988 b8e2439
            | exact resolve b8e2439 b8e1988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2439
          have b8e2494 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op X2 X2) ∨ (k X2 (M.op X1 X1)) = X2 := by
            intro X1 X2
            first
            | (have j0 := b8e2436 x X1 X2
               grind)
            | (have r₁ := b8e2436 X2 x X2
               have r₂ := b8e1988 x X2 x
               grind)
            | exact resolve b8e2436 b8e1988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2436
          have b8e3923 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e787 X3 (M.op (M.op X3 X0) X1) X2
               have i₂ := b8e1125 X0 X1 X3
               grind)
            | exact superpose b8e1125 b8e787
            | exact resolve b8e787 b8e1125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3931 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) = (M.op X2 (M.op (M.op (M.op X3 X4) X0) X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e28 X3 X4 X2 (M.op (M.op (M.op X3 X4) X0) X1)
               have i₂ := b8e1125 X0 X1 (M.op X3 X4)
               grind)
            | exact superpose b8e1125 b8e28
            | exact resolve b8e28 b8e1125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28 b8e1125
          have b8e3946 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op (M.op X3 X4) X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e3931 X0 X1 X2 X3 X4
               have i₂ := b8e1081 (M.op X3 X4) X1 X2 X0
               grind)
            | (have i₁ := b8e3931 X0 (M.op X0 X1) X2 X3 X4
               have i₂ := b8e1081 X0 X1 X2 (M.op (M.op X3 X4) X0)
               grind)
            | exact superpose b8e1081 b8e3931
            | exact resolve b8e3931 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3931
          have b8e3954 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X3 X1))) = (M.op X2 (M.op X3 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e3923 X3 X1 X2 X0
               have i₂ := b8e1998 X3 X0 X1
               grind)
            | exact superpose b8e1998 b8e3923
            | exact resolve b8e3923 b8e1998
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3923
          have b8e4011 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X4 (M.op X3 X1)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e3946 X0 X1 X2 X3 X4
               have i₂ := b8e1081 X3 X1 X0 X4
               grind)
            | (have i₁ := b8e3946 X2 (M.op X0 X1) X2 X3 X4
               have i₂ := b8e1081 X0 X1 X2 (M.op X3 X4)
               grind)
            | exact superpose b8e1081 b8e3946
            | exact resolve b8e3946 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3946
          have b8e4057 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X4 (M.op X3 X1)))) = (M.op X2 (M.op (M.op X3 X4) (M.op X0 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e4011 X0 X1 X2 X3 X4
               have i₂ := b8e1147 X3 X2 X4 (M.op X0 X1)
               grind)
            | exact superpose b8e1147 b8e4011
            | exact resolve b8e4011 b8e1147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1147 b8e4011
          have b8e4088 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X4 (M.op X3 X1)))) = (M.op X2 (M.op X4 (M.op X3 (M.op X0 X1)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e4057 X0 X1 X2 X3 X4
               have i₂ := b8e1081 X3 (M.op X0 X1) X2 X4
               grind)
            | (have i₁ := b8e4057 X0 X1 X2 X3 X4
               have i₂ := b8e1081 X0 X1 X2 (M.op X3 X4)
               grind)
            | exact superpose b8e1081 b8e4057
            | exact resolve b8e4057 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4057
          have b8e6279 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X1))) := by
            intro X0 X1
            grind
          clear b8e1836
          have b8e6364 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e6279 X0 X1
               have i₂ := b8e1081 X0 X1 X0 X1
               grind)
            | (have i₁ := b8e6279 x (M.op X0 X1)
               have i₂ := b8e1081 X0 X1 x (M.op x (M.op X0 X1))
               grind)
            | exact superpose b8e1081 b8e6279
            | exact resolve b8e6279 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6279
          have b8e6516 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e6364 X0 X1
               have i₂ := b8e1224 X1 X1 X0
               grind)
            | exact superpose b8e1224 b8e6364
            | exact resolve b8e6364 b8e1224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6364
          have b8e9288 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e2492 X1
               have i₂ := b8e55 X0 X1
               grind)
            | (have i₁ := b8e2492 X1
               have i₂ := b8e55 (M.op X1 X1) X1
               grind)
            | exact superpose b8e55 b8e2492
            | (have j1 := b8e55 X0 X1
               grind)
            | exact resolve b8e2492 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55 b8e2492
          have b8e9331 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e9288 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9288
          have b8e11397 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e18 X0 X0
               have i₂ := b8e9331 X0 X1
               grind)
            | exact superpose b8e9331 b8e18
            | (have j0 := b8e18 X0 X0
               have j1 := b8e9331 X0 X1
               grind)
            | exact resolve b8e18 b8e9331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11406 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e63 (σ y)
               have i₂ := b8e9331 (σ y) X0
               grind)
            | exact superpose b8e9331 b8e63
            | (have j0 := b8e63 (σ y)
               have j1 := b8e9331 (σ y) X0
               grind)
            | exact resolve b8e63 b8e9331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e11430 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e9331 X0 (τ X1)
               grind)
            | exact superpose b8e9331 b8e26
            | (have j1 := b8e9331 X0 X1
               grind)
            | exact resolve b8e26 b8e9331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11438 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e11406 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11406
          have b8e11444 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e11397 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11397
          have b8e11469 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b8e11438 X0
               grind)
            | (have r₁ := b8e11438 X0
               have r₂ := b8e24
               grind)
            | exact resolve b8e11438 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11438
          have b8e11647 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e34 X0 y
               have i₂ := b8e11469 X0
               grind)
            | exact superpose b8e11469 b8e34
            | exact resolve b8e34 b8e11469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e11651 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e11469 (σ X0)
               grind)
            | exact superpose b8e11469 b8e19
            | exact resolve b8e19 b8e11469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11680 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e2205 (M.op X0 X0)
               have i₂ := b8e6516 X0 X0
               grind)
            | exact superpose b8e6516 b8e2205
            | (have j0 := b8e2205 (M.op X0 X0)
               grind)
            | exact resolve b8e2205 b8e6516
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6516
          have b8e11685 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e2205 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e2205
            | (have j0 := b8e2205 (τ X0)
               grind)
            | exact resolve b8e2205 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e2205
          have b8e11687 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b8e11680 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11680
          have b8e11693 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e11685 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e11685
            | (have j0 := b8e11685 X0
               grind)
            | exact resolve b8e11685 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11685
          have b8e11702 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e11693 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e11693
            | (have j0 := b8e11693 X0
               grind)
            | exact resolve b8e11693 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11693
          have b8e11736 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e11702 (τ X0)
               have i₂ := b8e65 X0 X0
               grind)
            | exact superpose b8e65 b8e11702
            | (have j0 := b8e11702 (τ X0)
               grind)
            | exact resolve b8e11702 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e11978 : ∀ X0 X1 : G, (k (τ (M.op (σ y) X1)) y) = (τ (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e11647 (M.op (σ y) X1)
               have i₂ := b8e2377 (σ y) X1 X0
               grind)
            | (have i₁ := b8e11647 (M.op (σ y) X1)
               have i₂ := b8e2377 X0 X1 (σ y)
               grind)
            | exact superpose b8e2377 b8e11647
            | exact resolve b8e11647 b8e2377
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e12014 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (k (k (τ X1) y) y) := by
            intro X0 X1
            first
            | (have i₁ := b8e11978 X0 X1
               have i₂ := b8e11647 X1
               grind)
            | exact superpose b8e11647 b8e11978
            | exact resolve b8e11978 b8e11647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11647 b8e11978
          have b8e12650 : (σ y) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e11651 y
               grind)
            | exact superpose b8e11651 b8e24
            | exact resolve b8e24 b8e11651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e13080 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b8e12650
               have i₂ := b8e9331 y X0
               grind)
            | exact superpose b8e9331 b8e12650
            | (have j1 := b8e9331 y X0
               grind)
            | exact resolve b8e12650 b8e9331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9331 b8e12650
          have b8e13100 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b8e13080 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13080
          have b8e13231 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 y
               have i₂ := b8e13100 (τ X0)
               grind)
            | exact superpose b8e13100 b8e26
            | exact resolve b8e26 b8e13100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e13236 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e13231 X0
               have i₂ := b8e11469 X0
               grind)
            | exact superpose b8e11469 b8e13231
            | exact resolve b8e13231 b8e11469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11469 b8e13231
          have b8e13526 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e13236 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e13236
            | exact resolve b8e13236 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13236
          have b8e15221 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ y) (σ (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2377 X1 (σ X0) (σ y)
               have i₂ := b8e13526 X0
               grind)
            | exact superpose b8e13526 b8e2377
            | exact resolve b8e2377 b8e13526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13526
          have b8e15224 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (k (M.op y X0) y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e15221 X0 X1
               have i₂ := b8e11651 (M.op y X0)
               grind)
            | exact superpose b8e11651 b8e15221
            | exact resolve b8e15221 b8e11651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11651 b8e15221
          have b8e15257 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op y (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e15224 X0 X1
               have i₂ := b8e13100 (M.op y X0)
               grind)
            | exact superpose b8e13100 b8e15224
            | exact resolve b8e15224 b8e13100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15224
          have b8e79360 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (σ (M.op y (M.op y (τ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e15257 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e15257
            | exact resolve b8e15257 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79524 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (σ X1))) = (σ (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e15257 X1 X2
               have i₂ := b8e2377 y X1 X0
               grind)
            | (have i₁ := b8e15257 X1 X2
               have i₂ := b8e2377 X0 X1 y
               grind)
            | exact superpose b8e2377 b8e15257
            | exact resolve b8e15257 b8e2377
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e87117 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e79360 X1 X2
               have i₂ := b8e2377 y (τ X1) X0
               grind)
            | (have i₁ := b8e79360 X1 X2
               have i₂ := b8e2377 X0 (τ X1) y
               grind)
            | exact superpose b8e2377 b8e79360
            | exact resolve b8e79360 b8e2377
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2377 b8e79360
          have b8e130730 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            grind
          clear b8e2494
          have b8e130870 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e130730 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130730
          have b8e131433 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e41 X0 (M.op X1 X1)
               have i₂ := b8e130870 X1 (σ X0)
               grind)
            | exact superpose b8e130870 b8e41
            | exact resolve b8e41 b8e130870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e131440 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e131433 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e131433
            | exact resolve b8e131433 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131433
          have b8e133612 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e131440 X1 X0
               have i₂ := b8e11444 X0 X2
               grind)
            | exact superpose b8e11444 b8e131440
            | (have j1 := b8e11444 X0 X2
               grind)
            | exact resolve b8e131440 b8e11444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11444
          have b8e133716 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e11702 (τ (M.op X0 X0))
               have i₂ := b8e131440 (τ (M.op X0 X0)) X0
               grind)
            | exact superpose b8e131440 b8e11702
            | (have j0 := b8e11702 (τ (M.op X0 X0))
               grind)
            | (have r₁ := b8e11702 (τ (M.op x x))
               have r₂ := b8e131440 (τ (M.op x x)) x
               grind)
            | exact resolve b8e11702 b8e131440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131440
          have b8e133732 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b8e133716 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133716
          have b8e146617 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (τ (σ X0))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e133612 (σ X0) X2 (σ X1)
               grind)
            | exact superpose b8e133612 b8e19
            | (have j1 := b8e133612 (σ X0) X2 X2
               grind)
            | exact resolve b8e19 b8e133612
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133612
          have b8e146655 : ∀ X0 X1 X2 : G, (k X2 X0) = X2 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e146617 X0 X1 X2
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e146617
            | (have j0 := b8e146617 X0 X1 X2
               grind)
            | exact resolve b8e146617 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146617
          have b8e157305 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1004 X1 X2 (σ (M.op X0 X0))
               have i₂ := b8e11687 X0
               grind)
            | exact superpose b8e11687 b8e1004
            | exact resolve b8e1004 b8e11687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11687
          have b8e157815 : ∀ X0 X1 X3 : G, (σ (M.op X3 (M.op X3 X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e79524 X3 X1 x
               have i₂ := b8e157305 X0 x (σ X1)
               grind)
            | exact superpose b8e157305 b8e79524
            | exact resolve b8e79524 b8e157305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e157816 : ∀ X0 X1 : G, (σ (M.op y (M.op y X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e15257 X1 x
               have i₂ := b8e157305 X0 x (σ X1)
               grind)
            | exact superpose b8e157305 b8e15257
            | exact resolve b8e15257 b8e157305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15257 b8e157305
          have b8e191948 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (τ (M.op X0 X0)) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e775 (τ (M.op X0 X0)) X1 X2
               have i₂ := b8e133732 X0
               grind)
            | exact superpose b8e133732 b8e775
            | exact resolve b8e775 b8e133732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e775
          have b8e191949 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (τ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1004 X1 X2 (τ (M.op X0 X0))
               have i₂ := b8e133732 X0
               grind)
            | exact superpose b8e133732 b8e1004
            | exact resolve b8e1004 b8e133732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1004
          have b8e192088 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e191948 X0 X1 X2
               have i₂ := b8e1998 X1 (τ (M.op X0 X0)) X2
               grind)
            | exact superpose b8e1998 b8e191948
            | exact resolve b8e191948 b8e1998
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1998 b8e191948
          have b8e193746 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (τ (τ (M.op X0 X0))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e191949 (τ (M.op X0 X0)) X1 X2
               have i₂ := b8e133732 X0
               grind)
            | exact superpose b8e133732 b8e191949
            | exact resolve b8e191949 b8e133732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e193856 : ∀ X0 X1 X3 : G, (σ (M.op X3 (M.op X3 X1))) = (M.op (τ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e79524 X3 X1 x
               have i₂ := b8e191949 X0 x (σ X1)
               grind)
            | exact superpose b8e191949 b8e79524
            | exact resolve b8e79524 b8e191949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79524
          have b8e206892 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (τ (τ (τ (M.op X0 X0)))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e193746 (τ (M.op X0 X0)) X1 X2
               have i₂ := b8e133732 X0
               grind)
            | exact superpose b8e133732 b8e193746
            | exact resolve b8e193746 b8e133732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133732
          have b8e207164 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (τ (M.op X0 (M.op X0 (τ (τ (M.op X1 X1)))))) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e192088 (τ (τ (M.op X1 X1))) X2 X3
               have i₂ := b8e193746 X1 X0 (τ (τ (M.op X1 X1)))
               grind)
            | exact superpose b8e193746 b8e192088
            | exact resolve b8e192088 b8e193746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192088 b8e193746
          have b8e207443 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (k (k (τ (τ (τ (M.op X1 X1)))) y) y) X3)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e207164 x X1 X2 X3
               have i₂ := b8e12014 x (τ (τ (M.op X1 X1)))
               grind)
            | exact superpose b8e12014 b8e207164
            | exact resolve b8e207164 b8e12014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12014 b8e207164
          have b8e207854 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op y (k (τ (τ (τ (M.op X1 X1)))) y)) X3)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e207443 X1 X2 X3
               have i₂ := b8e13100 (k (τ (τ (τ (M.op X1 X1)))) y)
               grind)
            | exact superpose b8e13100 b8e207443
            | exact resolve b8e207443 b8e13100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207443
          have b8e208079 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (k (τ (τ (τ (M.op X1 X1)))) y) (M.op y X3))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e207854 X1 X2 X3
               have i₂ := b8e1081 y X3 X2 (k (τ (τ (τ (M.op X1 X1)))) y)
               grind)
            | (have i₁ := b8e207854 X1 X2 (M.op x X1)
               have i₂ := b8e1081 x X1 X2 (M.op y (k (τ (τ (τ (M.op X1 X1)))) y))
               grind)
            | exact superpose b8e1081 b8e207854
            | exact resolve b8e207854 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207854
          have b8e208209 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op y (M.op (k (τ (τ (τ (M.op X1 X1)))) y) X3))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e208079 X1 X2 X3
               have i₂ := b8e3954 (k (τ (τ (τ (M.op X1 X1)))) y) X3 X2 y
               grind)
            | (have i₁ := b8e208079 X1 X2 X3
               have i₂ := b8e3954 y X3 X2 (k (τ (τ (τ (M.op X1 X1)))) y)
               grind)
            | exact superpose b8e3954 b8e208079
            | exact resolve b8e208079 b8e3954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3954 b8e208079
          have b8e208292 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op y (M.op (M.op y (τ (τ (τ (M.op X1 X1))))) X3))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e208209 X1 X2 X3
               have i₂ := b8e13100 (τ (τ (τ (M.op X1 X1))))
               grind)
            | exact superpose b8e13100 b8e208209
            | exact resolve b8e208209 b8e13100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13100 b8e208209
          have b8e208349 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op y (M.op (τ (τ (τ (M.op X1 X1)))) (M.op y X3)))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e208292 X1 X2 X3
               have i₂ := b8e1081 y X3 y (τ (τ (τ (M.op X1 X1))))
               grind)
            | (have i₁ := b8e208292 X1 X2 (M.op x X1)
               have i₂ := b8e1081 x X1 y (M.op y (τ (τ (τ (M.op X1 X1)))))
               grind)
            | exact superpose b8e1081 b8e208292
            | exact resolve b8e208292 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208292
          have b8e208387 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op y (M.op y (M.op (τ (τ (τ (M.op X1 X1)))) X3)))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e208349 X1 X2 X3
               have i₂ := b8e4088 y X3 X2 (τ (τ (τ (M.op X1 X1)))) y
               grind)
            | (have i₁ := b8e208349 X1 X2 X1
               have i₂ := b8e4088 y X1 X2 y (τ (τ (τ (M.op X1 X1))))
               grind)
            | exact superpose b8e4088 b8e208349
            | exact resolve b8e208349 b8e4088
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4088 b8e208349
          have b8e208414 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (τ (τ (τ (M.op X1 X1)))) X3)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e208387 X1 X2 X3
               have i₂ := b8e787 y (M.op (τ (τ (τ (M.op X1 X1)))) X3) X2
               grind)
            | exact superpose b8e787 b8e208387
            | exact resolve b8e208387 b8e787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e787 b8e208387
          have b8e822312 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e11430 X1 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e11430
            | (have j0 := b8e11430 X1 X1
               grind)
            | exact resolve b8e11430 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11430
          have b8e822321 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e822312 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e822312
            | (have j0 := b8e822312 X0 X1
               grind)
            | exact resolve b8e822312 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e822312
          have b8e830411 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e11702 X0
               have i₂ := b8e822321 X1 X0
               grind)
            | exact superpose b8e822321 b8e11702
            | (have j0 := b8e11702 X0
               have j1 := b8e822321 X1 X0
               grind)
            | (have r₁ := b8e11702 X1
               have r₂ := b8e822321 X0 X1
               grind)
            | exact resolve b8e11702 b8e822321
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e822321
          have b8e830412 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e830411 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e830411
          have b8e837705 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e130870 X0 X1
               have i₂ := b8e830412 X0 X2
               grind)
            | exact superpose b8e830412 b8e130870
            | (have j1 := b8e830412 X0 X2
               grind)
            | exact resolve b8e130870 b8e830412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130870 b8e830412
          have b8e1006625 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e146655 x y X0
               grind)
            | exact superpose b8e146655 b8e20
            | (have j1 := b8e146655 x x X0
               grind)
            | exact resolve b8e20 b8e146655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146655
          have b8e1006652 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b8e1006625 X0
               have j1 := b8e837705 x X0 x
               grind)
            | (have r₁ := b8e1006625 X0
               have r₂ := b8e837705 x x y
               grind)
            | exact resolve b8e1006625 b8e837705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e837705 b8e1006625
          have b8e1012104 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e11702 x
               have i₂ := b8e1006652 x
               grind)
            | exact superpose b8e1006652 b8e11702
            | (have j0 := b8e11702 x
               grind)
            | (have r₁ := b8e11702 x
               have r₂ := b8e1006652 x
               grind)
            | exact resolve b8e11702 b8e1006652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11702
          have b8e1012105 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
            first
            | (have i₁ := b8e11736 x
               have i₂ := b8e1006652 x
               grind)
            | exact superpose b8e1006652 b8e11736
            | (have j0 := b8e11736 x
               grind)
            | exact resolve b8e11736 b8e1006652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11736 b8e1006652
          have b8e1012167 : (τ x) = (M.op (τ x) (τ x)) := by grind
          clear b8e1012105
          have b8e1012168 : x = (M.op x x) := by grind
          clear b8e1012104
          have b8e1017711 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b8e157816 x X0
               have i₂ := b8e1012168
               grind)
            | exact superpose b8e1012168 b8e157816
            | exact resolve b8e157816 b8e1012168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157816
          have b8e1017725 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (τ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e191949 x X0 X1
               have i₂ := b8e1012168
               grind)
            | exact superpose b8e1012168 b8e191949
            | exact resolve b8e191949 b8e1012168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e191949
          have b8e1017737 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (τ x) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e193856 x X1 X0
               have i₂ := b8e1012168
               grind)
            | exact superpose b8e1012168 b8e193856
            | exact resolve b8e193856 b8e1012168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e193856
          have b8e1017785 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (M.op (M.op X0 x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1127 X0 x x X1
               have i₂ := b8e1012168
               grind)
            | exact superpose b8e1012168 b8e1127
            | exact resolve b8e1127 b8e1012168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1127
          have b8e1017796 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e1988 x x x
               have i₂ := b8e1012168
               grind)
            | exact superpose b8e1012168 b8e1988
            | exact resolve b8e1988 b8e1012168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1988 b8e1012168
          have b8e1017892 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1017785 X0 X1
               have i₂ := b8e13 X0 X1 x
               grind)
            | exact superpose b8e13 b8e1017785
            | exact resolve b8e1017785 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017785
          have b8e1017914 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (τ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e1017711 X0
               have i₂ := b8e1017737 y X0
               grind)
            | exact superpose b8e1017737 b8e1017711
            | exact resolve b8e1017711 b8e1017737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017711
          have b8e1064622 : ∀ X1 : G, x = (σ (M.op X1 (M.op X1 (τ x)))) := by
            intro X1
            first
            | (have i₁ := b8e87117 X1 x x
               have i₂ := b8e1017796 x
               grind)
            | exact superpose b8e1017796 b8e87117
            | exact resolve b8e87117 b8e1017796
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87117
          have b8e1064923 : ∀ X0 X1 : G, x = (M.op X0 (M.op X0 (M.op (τ (τ (τ (M.op X1 X1)))) x))) := by
            intro X0 X1
            first
            | (have i₁ := b8e206892 X1 X0 (M.op (τ (τ (τ (M.op X1 X1)))) x)
               have i₂ := b8e1017796 (τ (τ (τ (M.op X1 X1))))
               grind)
            | exact superpose b8e1017796 b8e206892
            | exact resolve b8e206892 b8e1017796
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e206892 b8e1017796
          have b8e1064954 : ∀ X1 : G, x = (M.op (τ x) (M.op (τ (τ (τ (M.op X1 X1)))) x)) := by
            intro X1
            first
            | (have i₁ := b8e1064923 x X1
               have i₂ := b8e1017725 x (M.op (τ (τ (τ (M.op X1 X1)))) x)
               grind)
            | exact superpose b8e1017725 b8e1064923
            | exact resolve b8e1064923 b8e1017725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1064923
          have b8e1065110 : x = (M.op (τ x) (σ (τ x))) := by
            first
            | (have i₁ := b8e1064622 x
               have i₂ := b8e1017737 x (τ x)
               grind)
            | exact superpose b8e1017737 b8e1064622
            | exact resolve b8e1064622 b8e1017737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017737 b8e1064622
          have b8e1065250 : x = (M.op (τ x) x) := by
            first
            | (have i₁ := b8e1064954 x
               have i₂ := b8e208414 x (τ x) x
               grind)
            | (have i₁ := b8e1064954 x
               have i₂ := b8e208414 x (τ x) (M.op (τ (τ (τ (M.op x x)))) x)
               grind)
            | exact superpose b8e208414 b8e1064954
            | exact resolve b8e1064954 b8e208414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208414 b8e1064954
          have b8e1065349 : x = (M.op (σ x) (σ (τ x))) := by
            first
            | (have i₁ := b8e1065110
               have i₂ := b8e1017914 (τ x)
               grind)
            | exact superpose b8e1017914 b8e1065110
            | exact resolve b8e1065110 b8e1017914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017914 b8e1065110
          have b8e1065479 : x = (M.op (σ x) x) := by
            first
            | (have i₁ := b8e1065349
               have i₂ := b8e15 x
               grind)
            | exact superpose b8e15 b8e1065349
            | exact resolve b8e1065349 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1065349
          have b8e1070628 : ∀ X0 X1 : G, (M.op (τ x) X0) = (M.op x (M.op X1 (M.op (M.op X1 x) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1128 (τ x) X0 X1 x
               have i₂ := b8e1065250
               grind)
            | exact superpose b8e1065250 b8e1128
            | exact resolve b8e1128 b8e1065250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1065250
          have b8e1070749 : ∀ X0 X1 : G, (M.op (τ x) X0) = (M.op X1 (M.op (M.op X1 x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1070628 X0 X1
               have i₂ := b8e1017892 X1 (M.op (M.op X1 x) X0)
               grind)
            | exact superpose b8e1017892 b8e1070628
            | exact resolve b8e1070628 b8e1017892
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1070628
          have b8e1070778 : ∀ X0 X1 : G, (M.op (τ x) X0) = (M.op X1 (M.op x (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1070749 X0 X1
               have i₂ := b8e1081 X1 X0 X1 x
               grind)
            | (have i₁ := b8e1070749 (M.op X0 X1) x
               have i₂ := b8e1081 X0 X1 x (M.op x x)
               grind)
            | exact superpose b8e1081 b8e1070749
            | exact resolve b8e1070749 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1070749
          have b8e1070798 : ∀ X0 : G, (M.op x X0) = (M.op (τ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e1070778 X0 x
               have i₂ := b8e1224 x X0 x
               grind)
            | exact superpose b8e1224 b8e1070778
            | exact resolve b8e1070778 b8e1224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1070778
          have b8e1077063 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op x (M.op X1 (M.op (M.op X1 x) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1128 (σ x) X0 X1 x
               have i₂ := b8e1065479
               grind)
            | exact superpose b8e1065479 b8e1128
            | exact resolve b8e1128 b8e1065479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1128 b8e1065479
          have b8e1077190 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op X1 (M.op (M.op X1 x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1077063 X0 X1
               have i₂ := b8e1017892 X1 (M.op (M.op X1 x) X0)
               grind)
            | exact superpose b8e1017892 b8e1077063
            | exact resolve b8e1077063 b8e1017892
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017892 b8e1077063
          have b8e1077226 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op X1 (M.op x (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1077190 X0 X1
               have i₂ := b8e1081 X1 X0 X1 x
               grind)
            | (have i₁ := b8e1077190 (M.op X0 X1) x
               have i₂ := b8e1081 X0 X1 x (M.op x x)
               grind)
            | exact superpose b8e1081 b8e1077190
            | exact resolve b8e1077190 b8e1081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1081 b8e1077190
          have b8e1077248 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e1077226 X0 x
               have i₂ := b8e1224 x X0 x
               grind)
            | exact superpose b8e1224 b8e1077226
            | exact resolve b8e1077226 b8e1224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1224 b8e1077226
          have b8e1083046 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (τ x)) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e157815 (τ x) X1 X0
               have i₂ := b8e1012167
               grind)
            | exact superpose b8e1012167 b8e157815
            | exact resolve b8e157815 b8e1012167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157815 b8e1012167
          have b8e1083295 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op x (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1083046 X0 X1
               have i₂ := b8e15 x
               grind)
            | exact superpose b8e15 b8e1083046
            | exact resolve b8e1083046 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1083046
          have b8e1083379 : ∀ X1 : G, (M.op x (σ X1)) = (σ (M.op (τ x) X1)) := by
            intro X1
            first
            | (have i₁ := b8e1083295 x X1
               have i₂ := b8e1017725 x X1
               grind)
            | exact superpose b8e1017725 b8e1083295
            | exact resolve b8e1083295 b8e1017725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017725 b8e1083295
          have b8e1083414 : ∀ X1 : G, (M.op x (σ X1)) = (σ (M.op x X1)) := by
            intro X1
            first
            | (have i₁ := b8e1083379 X1
               have i₂ := b8e1070798 X1
               grind)
            | exact superpose b8e1070798 b8e1083379
            | exact resolve b8e1083379 b8e1070798
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1070798 b8e1083379
          have b8e1152260 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1077248 (σ y)
               grind)
            | exact superpose b8e1077248 b8e20
            | exact resolve b8e20 b8e1077248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1077248
          have b8e1152827 : False := by grind
          exact b8e1152827

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation3591 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y y) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e27 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e10 y X0 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X3 (M.op (M.op X0 X2) X1)
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 (M.op (M.op X0 y) X1)
           have i₂ := b0e10 X0 X1 y
           grind)
        | exact superpose b0e10 b0e27
        | exact resolve b0e27 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e13 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e13
        | (have j0 := b0e13 X1 X0
           have j1 := b0e14 X2 X0
           grind)
        | (have r₁ := b0e13 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e13 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e38 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e48 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e33 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e33
        | exact resolve b0e33 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 y X2 (M.op X0 X1)
           have i₂ := b0e33 X0 X1
           grind)
        | exact superpose b0e33 b0e10
        | exact resolve b0e10 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e58 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e14 (τ X1) X0
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 X0 X0
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k (τ X0) X1)
           have i₂ := b0e23 X0 X1
           grind)
        | exact superpose b0e23 b0e11
        | exact resolve b0e11 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e116 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e44 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e44 b0e15
        | (have j1 := b0e44 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e133 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e29 X0 X2 X0 X1
           have i₂ := b0e14 X3 X0
           grind)
        | exact superpose b0e14 b0e29
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e29 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e139 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op (M.op (M.op y X0) X2) (M.op (M.op y X2) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29 y X2 (M.op y X0) X1
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e29
        | exact resolve b0e29 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e151 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op y X0) y) (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 y y X0 X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e29
        | exact resolve b0e29 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e156 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e29 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
           have i₂ := b0e10 X0 X1 (M.op X3 X4)
           grind)
        | exact superpose b0e10 b0e29
        | exact resolve b0e29 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e168 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y (M.op y y)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e151 X0 X1
           have i₂ := b0e156 y X1 X0 y y
           grind)
        | exact superpose b0e156 b0e151
        | exact resolve b0e151 b0e156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151 b0e156
      have b0e180 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e139 X0 X1 x
           have i₂ := b0e29 y x X0 X1
           grind)
        | exact superpose b0e29 b0e139
        | exact resolve b0e139 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e139
      have b0e185 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y X1) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e133 X0 X1 x X3
           have i₂ := b0e54 X0 x X1
           grind)
        | exact superpose b0e54 b0e133
        | (have j0 := b0e133 X0 X1 x X3
           grind)
        | exact resolve b0e133 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54 b0e133
      have b0e189 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op y y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e168 X0 X1
           have i₂ := b0e27 y
           grind)
        | exact superpose b0e27 b0e168
        | exact resolve b0e168 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e168
      have b0e199 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e189 X0 X1
           have i₂ := b0e180 y X1
           grind)
        | exact superpose b0e180 b0e189
        | exact resolve b0e189 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e189
      have b0e209 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op (M.op y X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e29 y X1 X0 X2
           have i₂ := b0e180 X0 X1
           grind)
        | exact superpose b0e180 b0e29
        | exact resolve b0e29 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e210 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 y X1 X0
           have i₂ := b0e180 X0 X1
           grind)
        | exact superpose b0e180 b0e10
        | exact resolve b0e10 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e224 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e209 X0 X1 X2
           have i₂ := b0e180 X1 X2
           grind)
        | exact superpose b0e180 b0e209
        | exact resolve b0e209 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180 b0e209
      have b0e584 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 X1 (σ X0)
           have i₂ := b0e41 X0 X0
           grind)
        | exact superpose b0e41 b0e13
        | (have j0 := b0e13 X1 (σ X0)
           have j1 := b0e41 X0 X1
           grind)
        | (have r₁ := b0e13 X0 (σ X0)
           have r₂ := b0e41 X0 X1
           grind)
        | exact resolve b0e13 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e600 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e41 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e584 X0 X1
           have j1 := b0e13 X1 (σ X0)
           grind)
        | (have r₁ := b0e584 X0 X1
           have r₂ := b0e13 X0 (σ X0)
           grind)
        | exact resolve b0e584 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e584
      have b0e1149 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e61 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e61
        | exact resolve b0e61 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e1574 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e609 (τ X0) X1
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e609
        | (have j0 := b0e609 (τ X0) X1
           grind)
        | exact resolve b0e609 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1586 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1574 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1574
        | (have j0 := b0e1574 X0 X1
           grind)
        | exact resolve b0e1574 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1574
      have b0e1593 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1586 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1586
        | (have j0 := b0e1586 X0 X1
           grind)
        | exact resolve b0e1586 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1586
      have b0e1819 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e185 (σ x) (σ y) X0
           grind)
        | exact superpose b0e185 b0e16
        | (have j1 := b0e185 (σ x) x X0
           grind)
        | exact resolve b0e16 b0e185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e185
      have b0e1881 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e1819 X0
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e1819
        | (have j0 := b0e1819 X0
           grind)
        | exact resolve b0e1819 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e1819
      have b0e2016 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e58 X1 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e58
        | (have j0 := b0e58 X1 X1
           grind)
        | exact resolve b0e58 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e2094 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e2016 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e2016
        | (have j0 := b0e2016 X0 X1
           grind)
        | exact resolve b0e2016 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2016
      have b0e2159 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1593 (τ X0) X1
           have i₂ := b0e1149 X0 X0
           grind)
        | exact superpose b0e1149 b0e1593
        | (have j0 := b0e1593 (τ X0) X1
           grind)
        | exact resolve b0e1593 b0e1149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1149 b0e1593
      have b0e2445 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e224 X1 X2 (M.op X2 X0)
           have i₂ := b0e210 X2 X0
           grind)
        | exact superpose b0e210 b0e224
        | exact resolve b0e224 b0e210
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e224
      have b0e2538 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X1 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e2445 X0 X1 X2
           have i₂ := b0e199 (M.op X1 X2) X0
           grind)
        | exact superpose b0e199 b0e2445
        | exact resolve b0e2445 b0e199
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e199 b0e2445
      have b0e3561 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e600 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e600
        | (have j0 := b0e600 (τ X0)
           grind)
        | exact resolve b0e600 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e600
      have b0e3579 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e3561 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3561
        | (have j0 := b0e3561 X0
           grind)
        | exact resolve b0e3561 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3561
      have b0e3590 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e3579 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3579
        | (have j0 := b0e3579 X0
           grind)
        | exact resolve b0e3579 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3579
      have b0e4038 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e116 x y X0
           grind)
        | exact superpose b0e116 b0e16
        | (have j1 := b0e116 x x X0
           grind)
        | exact resolve b0e16 b0e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116
      have b0e108360 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e4038 X0
           have i₂ := b0e2094 y x
           grind)
        | exact superpose b0e2094 b0e4038
        | (have j0 := b0e4038 X0
           have j1 := b0e2094 X0 x
           grind)
        | (have r₁ := b0e4038 X0
           have r₂ := b0e2094 y x
           grind)
        | exact resolve b0e4038 b0e2094
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2094 b0e4038
      have b0e108362 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e108360 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108360
      have b0e108402 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e2159 (σ x) X0
           have i₂ := b0e108362 (σ x)
           grind)
        | exact superpose b0e108362 b0e2159
        | (have j0 := b0e2159 (σ x) X0
           grind)
        | exact resolve b0e2159 b0e108362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2159 b0e108362
      have b0e108442 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e108402 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108402
      have b0e108460 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e108442 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e108442
        | exact resolve b0e108442 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108442
      have b0e108471 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e108460 X0
           have j1 := b0e13 X0 x
           grind)
        | (have r₁ := b0e108460 X0
           have r₂ := b0e13 X0 x
           grind)
        | exact resolve b0e108460 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108460
      have b0e108688 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e609 x X0
           have i₂ := b0e108471 x
           grind)
        | exact superpose b0e108471 b0e609
        | (have j0 := b0e609 x X0
           grind)
        | exact resolve b0e609 b0e108471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e609
      have b0e108692 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e3590 x
           have i₂ := b0e108471 x
           grind)
        | exact superpose b0e108471 b0e3590
        | (have j0 := b0e3590 x
           grind)
        | (have r₁ := b0e3590 x
           have r₂ := b0e108471 x
           grind)
        | exact resolve b0e3590 b0e108471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3590 b0e108471
      have b0e108735 : x = (M.op x x) := by grind
      clear b0e108692
      have b0e108738 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have j0 := b0e108688 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108688
      have b0e109055 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e2538 X0 x x
           have i₂ := b0e108735
           grind)
        | exact superpose b0e108735 b0e2538
        | exact resolve b0e2538 b0e108735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2538 b0e108735
      have b0e109070 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e109055 X0
           have i₂ := b0e210 x X0
           grind)
        | exact superpose b0e210 b0e109055
        | exact resolve b0e109055 b0e210
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210 b0e109055
      have b0e110808 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e1881 X0
           have i₂ := b0e109070 y
           grind)
        | exact superpose b0e109070 b0e1881
        | (have j0 := b0e1881 X0
           grind)
        | exact resolve b0e1881 b0e109070
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1881
      have b0e111118 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e110808 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e110808
        | (have j0 := b0e110808 X0
           grind)
        | exact resolve b0e110808 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110808
      have b0e111119 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e111118 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111118
      have b0e111220 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e111119 X0
           have i₂ := b0e108738 X0
           grind)
        | exact superpose b0e108738 b0e111119
        | exact resolve b0e111119 b0e108738
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108738 b0e111119
      have b0e111720 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e111220 (σ y)
           grind)
        | exact superpose b0e111220 b0e16
        | exact resolve b0e16 b0e111220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111220
      have b0e112010 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e111720
           have i₂ := b0e109070 y
           grind)
        | exact superpose b0e109070 b0e111720
        | exact resolve b0e111720 b0e109070
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109070 b0e111720
      have b0e112075 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e112010
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e112010
        | exact resolve b0e112010 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112010
      have b0e112076 : False := by grind
      exact b0e112076
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 X0 y
           grind)
        | (have r₁ := b1e13 X0 y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e21 X0 y
           have i₂ := b1e20 (τ X0)
           grind)
        | exact superpose b1e20 b1e21
        | exact resolve b1e21 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e21
      have b1e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e45 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e28 X0
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e28
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e28 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e49 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e45 X0
           grind)
        | (have r₁ := b1e45 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e45 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e45 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e53 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e49 (σ y)
           grind)
        | exact superpose b1e49 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e49 (σ y)
           grind)
        | exact resolve b1e18 b1e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e58 : False := by grind
      exact b1e58
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y y) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 X0 (σ y)
           grind)
        | (have r₁ := b2e13 X0 (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b2e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e24 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e20 (σ X0)
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e27 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e11 (k X0 y)
           have i₂ := b2e24 X0
           grind)
        | exact superpose b2e24 b2e11
        | exact resolve b2e11 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e28 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e27 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e27
        | exact resolve b2e27 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e42 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e28 X0
           have i₂ := b2e14 X0 y
           grind)
        | exact superpose b2e14 b2e28
        | (have j1 := b2e14 X0 y
           grind)
        | exact resolve b2e28 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e46 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e42 X0
           grind)
        | (have r₁ := b2e42 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e42 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e42 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42
      have b2e49 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e46 y
           grind)
        | exact superpose b2e46 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e46 y
           grind)
        | exact resolve b2e17 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e54 : False := by grind
      exact b2e54
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 X3 (M.op (M.op X0 X2) X1)
           have i₂ := b3e10 X0 X1 X2
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
           have i₂ := b3e10 X0 X1 (M.op X2 X3)
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e19 X0 X1
           grind)
        | exact superpose b3e19 b3e11
        | exact resolve b3e11 b3e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 X0
           have i₂ := b3e14 X2 X0
           grind)
        | exact superpose b3e14 b3e13
        | (have j0 := b3e13 X1 X0
           have j1 := b3e14 X2 X0
           grind)
        | (have r₁ := b3e13 X0 X1
           have r₂ := b3e14 X0 X1
           grind)
        | exact resolve b3e13 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e31 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 X0 (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 X0 (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 X0 X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e34 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have j0 := b3e31 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31
      have b3e35 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e28 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e28
      have b3e37 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e34 (σ X0)
           grind)
        | exact superpose b3e34 b3e15
        | exact resolve b3e15 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e26 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e26
        | exact resolve b3e26 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26
      have b3e70 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e35 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e35 b3e15
        | (have j1 := b3e35 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e80 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e37 y
           grind)
        | exact superpose b3e37 b3e18
        | exact resolve b3e18 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e96 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e21 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
           have i₂ := b3e21 X4 X5 X0 X1
           grind)
        | exact superpose b3e21 b3e21
        | exact resolve b3e21 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e98 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e21 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
           have i₂ := b3e10 X0 X1 (M.op X3 X4)
           grind)
        | exact superpose b3e10 b3e21
        | exact resolve b3e21 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e101 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
           have i₂ := b3e21 X2 X3 X0 X1
           grind)
        | exact superpose b3e21 b3e10
        | exact resolve b3e10 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e104 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
           have i₂ := b3e21 X2 X3 X0 X1
           grind)
        | exact superpose b3e21 b3e10
        | exact resolve b3e10 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e106 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e96 X0 X1 X2 X3 X4 X5
           have i₂ := b3e98 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
           grind)
        | exact superpose b3e98 b3e96
        | exact resolve b3e96 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e96
      have b3e115 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e106 X0 X1 X2 X3 x x
           have i₂ := b3e21 x x X0 X1
           grind)
        | exact superpose b3e21 b3e106
        | exact resolve b3e106 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e106
      have b3e119 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e80
           have i₂ := b3e35 y y X0
           grind)
        | exact superpose b3e35 b3e80
        | (have j1 := b3e35 y x X0
           grind)
        | exact resolve b3e80 b3e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35 b3e80
      have b3e121 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e119 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e119
      have b3e125 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e22 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
           have i₂ := b3e22 X1 X2 X3 X0
           grind)
        | exact superpose b3e22 b3e22
        | exact resolve b3e22 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e132 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e22 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
           have i₂ := b3e21 X2 X3 X0 X1
           grind)
        | exact superpose b3e21 b3e22
        | exact resolve b3e22 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e138 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e21 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
           have i₂ := b3e22 X1 X2 X3 X0
           grind)
        | exact superpose b3e22 b3e21
        | exact resolve b3e21 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e140 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e21 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
           have i₂ := b3e22 X1 X2 (M.op X4 X5) X0
           grind)
        | exact superpose b3e22 b3e21
        | exact resolve b3e21 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e140 X0 X1 X2 X3 X4 X5
           have i₂ := b3e98 X0 (M.op X1 X2) X3 X4 X5
           grind)
        | exact superpose b3e98 b3e140
        | exact resolve b3e140 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e140
      have b3e146 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e138 X0 X1 X2 X3 X4 x
           have i₂ := b3e104 X3 x X0 (M.op X1 X2) X4
           grind)
        | exact superpose b3e104 b3e138
        | exact resolve b3e138 b3e104
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e104 b3e138
      have b3e154 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e125 X0 X1 X2 X3 X4 X5
           have i₂ := b3e98 X4 X5 (M.op X3 X0) X1 X2
           grind)
        | exact superpose b3e98 b3e125
        | exact resolve b3e125 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e125
      have b3e161 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e121 (τ X0)
           grind)
        | exact superpose b3e121 b3e19
        | exact resolve b3e19 b3e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e163 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e161 X0
           have i₂ := b3e34 X0
           grind)
        | exact superpose b3e34 b3e161
        | exact resolve b3e161 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34 b3e161
      have b3e205 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13 X1 (σ X0)
           have i₂ := b3e32 X0 X0
           grind)
        | exact superpose b3e32 b3e13
        | (have j0 := b3e13 X1 (σ X0)
           have j1 := b3e32 X0 X1
           grind)
        | (have r₁ := b3e13 X0 (σ X0)
           have r₂ := b3e32 X0 X1
           grind)
        | exact resolve b3e13 b3e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e219 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e32 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32
      have b3e227 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e205 X0 X1
           have j1 := b3e13 X1 (σ X0)
           grind)
        | (have r₁ := b3e205 X0 X1
           have r₂ := b3e13 X0 (σ X0)
           grind)
        | exact resolve b3e205 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e205
      have b3e476 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e227 (τ X0) X1
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e227
        | (have j0 := b3e227 (τ X0) X1
           grind)
        | exact resolve b3e227 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e227
      have b3e479 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e476 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e476
        | (have j0 := b3e476 X0 X1
           grind)
        | exact resolve b3e476 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e476
      have b3e483 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e479 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e479
        | (have j0 := b3e479 X0 X1
           grind)
        | exact resolve b3e479 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e479
      have b3e496 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e483 (τ X0) X1
           have i₂ := b3e48 X0 X0
           grind)
        | exact superpose b3e48 b3e483
        | (have j0 := b3e483 (τ X0) X1
           grind)
        | exact resolve b3e483 b3e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e48 b3e483
      have b3e531 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e163 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e163
        | exact resolve b3e163 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e163
      have b3e606 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e33 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e33
        | (have j0 := b3e33 X1 X1
           grind)
        | exact resolve b3e33 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e662 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e606 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e606
        | (have j0 := b3e606 X0 X1
           grind)
        | exact resolve b3e606 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e606
      have b3e1057 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) (M.op X3 X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e101 X3 X4 X2 (M.op (M.op X0 X2) X1)
           have i₂ := b3e10 X0 X1 X2
           grind)
        | exact superpose b3e10 b3e101
        | exact resolve b3e101 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1091 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X2 (M.op X0 X1)
           have i₂ := b3e101 X1 X2 X0 (M.op X0 X1)
           grind)
        | exact superpose b3e101 b3e10
        | exact resolve b3e10 b3e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1092 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e22 (M.op X3 X1) X4 (M.op X3 X0) X2
           have i₂ := b3e101 X1 X2 X3 X0
           grind)
        | exact superpose b3e101 b3e22
        | exact resolve b3e22 b3e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1094 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op (M.op X3 X0) X2) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 (M.op X3 X1) X4 (M.op (M.op X3 X0) X2)
           have i₂ := b3e101 X1 X2 X3 X0
           grind)
        | exact superpose b3e101 b3e10
        | exact resolve b3e10 b3e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1097 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e22 X4 X5 (M.op X3 X1) (M.op (M.op X3 X0) X2)
           have i₂ := b3e101 X1 X2 X3 X0
           grind)
        | exact superpose b3e101 b3e22
        | exact resolve b3e22 b3e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e101
      have b3e1104 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e1097 X0 X1 X2 X3 X4 X5
           have i₂ := b3e154 X1 X0 (M.op X1 X2) X3 X4 X5
           grind)
        | exact superpose b3e154 b3e1097
        | exact resolve b3e1097 b3e154
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1097
      have b3e1107 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1094 X0 X1 X2 X3 X4
           have i₂ := b3e98 (M.op X0 (M.op X1 X2)) X4 X0 X3 X2
           grind)
        | exact superpose b3e98 b3e1094
        | exact resolve b3e1094 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1094
      have b3e1109 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1092 X0 X1 X2 X3 X4
           have i₂ := b3e154 X0 X1 X2 X3 X0 X4
           grind)
        | exact superpose b3e154 b3e1092
        | exact resolve b3e1092 b3e154
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e154 b3e1092
      have b3e1125 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1057 X0 X1 X2 X3 X4
           have i₂ := b3e98 X3 X4 X2 X0 X1
           grind)
        | exact superpose b3e98 b3e1057
        | exact resolve b3e1057 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1057
      have b3e1131 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) = (M.op X0 (M.op (M.op X4 (M.op X3 X2)) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e1104 X0 X1 X2 X3 X4 X5
           have i₂ := b3e98 X4 X5 X0 X3 X2
           grind)
        | exact superpose b3e98 b3e1104
        | exact resolve b3e1104 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e98 b3e1104
      have b3e1134 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X3 X2))) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1107 X0 X1 X2 X3 X4
           have i₂ := b3e146 X2 X0 (M.op X3 X2) X1 X4
           grind)
        | (have i₁ := b3e1107 X0 X1 X2 X1 X4
           have i₂ := b3e146 X0 X1 X2 (M.op X1 X2) X4
           grind)
        | exact superpose b3e146 b3e1107
        | exact resolve b3e1107 b3e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1107
      have b3e1144 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op X3 X2) (M.op (M.op X2 X1) X4)) := by
        intro X1 X2 X3 X4
        first
        | (have i₁ := b3e1134 x X1 X2 X3 X4
           have i₂ := b3e22 (M.op X2 X1) X4 x (M.op X3 X2)
           grind)
        | exact superpose b3e22 b3e1134
        | exact resolve b3e1134 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1134
      have b3e1149 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X3 (M.op (M.op X2 (M.op X2 X1)) X4)) := by
        intro X1 X2 X3 X4
        first
        | (have i₁ := b3e1144 X1 X2 X3 X4
           have i₂ := b3e1125 X2 X1 X3 X2 X4
           grind)
        | (have i₁ := b3e1144 (M.op x X1) X3 X3 X4
           have i₂ := b3e1125 x X1 (M.op X3 X3) X3 X4
           grind)
        | exact superpose b3e1125 b3e1144
        | exact resolve b3e1144 b3e1125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1144
      have b3e1157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1091 X3 (M.op (M.op X1 (M.op X3 X0)) X2) X4
           have i₂ := b3e22 X1 X2 X3 X0
           grind)
        | exact superpose b3e22 b3e1091
        | exact resolve b3e1091 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1167 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X1) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1091 (M.op (M.op X2 X0) X3) (M.op (M.op X2 X3) X1) X4
           have i₂ := b3e21 X2 X3 X0 X1
           grind)
        | exact superpose b3e21 b3e1091
        | exact resolve b3e1091 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1169 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1091 (M.op X0 X2) (M.op X2 X1) X3
           have i₂ := b3e1091 X0 X2 X1
           grind)
        | exact superpose b3e1091 b3e1091
        | exact resolve b3e1091 b3e1091
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1170 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op (M.op X2 X3) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1091 X2 X3 (M.op (M.op X0 X3) X1)
           have i₂ := b3e10 X0 X1 X3
           grind)
        | exact superpose b3e10 b3e1091
        | exact resolve b3e1091 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1188 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X0 X2) X3) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e21 X0 X3 X2 (M.op X3 X1)
           have i₂ := b3e1091 X0 X3 X1
           grind)
        | exact superpose b3e1091 b3e21
        | exact resolve b3e21 b3e1091
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1190 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X2 (M.op X0 X1) X0
           have i₂ := b3e1091 X2 X0 X1
           grind)
        | exact superpose b3e1091 b3e10
        | exact resolve b3e10 b3e1091
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1193 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e22 (M.op X0 X1) X3 X1 X2
           have i₂ := b3e1091 X0 X1 X2
           grind)
        | exact superpose b3e1091 b3e22
        | exact resolve b3e22 b3e1091
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e22
      have b3e1197 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op X0 X2) X4) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e21 (M.op X0 X2) X4 (M.op X2 X1) X3
           have i₂ := b3e1091 X0 X2 X1
           grind)
        | exact superpose b3e1091 b3e21
        | exact resolve b3e21 b3e1091
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1091
      have b3e1209 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1197 X0 X1 X2 X3 X4
           have i₂ := b3e132 X2 (M.op (M.op X0 X1) X4) X0 X4 X3
           grind)
        | (have i₁ := b3e1197 X0 X1 X2 X4 X1
           have i₂ := b3e132 (M.op X0 X2) X1 (M.op X0 X1) X1 X4
           grind)
        | exact superpose b3e132 b3e1197
        | exact resolve b3e1197 b3e132
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e132 b3e1197
      have b3e1213 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1188 X0 X1 X2 X3
           have i₂ := b3e1190 X0 X1 (M.op (M.op X0 X2) X3)
           grind)
        | (have i₁ := b3e1188 X0 X1 X2 X3
           have i₂ := b3e1190 (M.op (M.op X0 X2) X3) X1 X0
           grind)
        | exact superpose b3e1190 b3e1188
        | exact resolve b3e1188 b3e1190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1188
      have b3e1221 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X1 (M.op (M.op X2 (M.op X0 X1)) X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1169 X0 X1 X2 X3
           have i₂ := b3e1193 X2 (M.op X0 X1) X1 X3
           grind)
        | (have i₁ := b3e1169 X0 X1 X2 X3
           have i₂ := b3e1193 X2 X1 (M.op X0 X1) X3
           grind)
        | exact superpose b3e1193 b3e1169
        | exact resolve b3e1169 b3e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1169
      have b3e1223 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op X1 (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1167 X0 X1 X2 X3 X4
           have i₂ := b3e1193 (M.op X2 X3) (M.op X0 X1) X1 X4
           grind)
        | (have i₁ := b3e1167 X0 X1 X2 X3 X4
           have i₂ := b3e1193 (M.op X2 X3) X1 (M.op X0 X1) X4
           grind)
        | exact superpose b3e1193 b3e1167
        | exact resolve b3e1167 b3e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1167
      have b3e1229 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2))) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1157 X0 X1 X2 X3 X4
           have i₂ := b3e1193 (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2)) X2 X4
           grind)
        | (have i₁ := b3e1157 X0 X1 X2 X3 X4
           have i₂ := b3e1193 (M.op X1 (M.op X3 X0)) X2 (M.op X0 (M.op X1 X2)) X4
           grind)
        | exact superpose b3e1193 b3e1157
        | exact resolve b3e1157 b3e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1157
      have b3e1234 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X4 (M.op X0 X1)) (M.op X2 X3))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1209 X0 X1 X2 X3 X4
           have i₂ := b3e144 X4 X2 X3 (M.op X0 X4) X0 X1
           grind)
        | (have i₁ := b3e1209 X0 X1 X0 (M.op X1 X2) x
           have i₂ := b3e144 X0 X1 X2 (M.op X0 x) (M.op X0 X1) x
           grind)
        | exact superpose b3e144 b3e1209
        | exact resolve b3e1209 b3e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1209
      have b3e1241 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op X0 (M.op X2 X3)) X4) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b3e1223 X0 x X2 X3 X4
           have i₂ := b3e1221 X0 x (M.op X2 X3) X4
           grind)
        | exact superpose b3e1221 b3e1223
        | exact resolve b3e1223 b3e1221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1221 b3e1223
      have b3e1244 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X1 (M.op X0 (M.op X1 X2)))) X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1229 X0 X1 X2 X3 X4
           have i₂ := b3e146 X0 X1 (M.op X0 (M.op X1 X2)) X3 X4
           grind)
        | (have i₁ := b3e1229 X1 X0 X2 X3 X4
           have i₂ := b3e146 X0 X1 (M.op X0 X2) (M.op X3 X1) X4
           grind)
        | exact superpose b3e146 b3e1229
        | exact resolve b3e1229 b3e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e146 b3e1229
      have b3e1248 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op (M.op X4 (M.op X4 (M.op X0 X1))) (M.op X2 X3))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1234 X0 X1 X2 X3 X4
           have i₂ := b3e1125 X4 (M.op X0 X1) X0 X4 (M.op X2 X3)
           grind)
        | (have i₁ := b3e1234 X0 X1 X2 X3 X3
           have i₂ := b3e1125 X0 X1 (M.op X0 X3) X3 (M.op X2 X3)
           grind)
        | exact superpose b3e1125 b3e1234
        | exact resolve b3e1234 b3e1125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1125 b3e1234
      have b3e1252 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op (M.op X0 X3) (M.op X2 X2)) X4)) := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b3e1244 X0 x X2 X3 X4
           have i₂ := b3e1131 X0 x X2 X2 (M.op X0 X3) X4
           grind)
        | exact superpose b3e1131 b3e1244
        | exact resolve b3e1244 b3e1131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1131 b3e1244
      have b3e1254 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op (M.op X0 X0) (M.op X2 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1248 X0 X1 X2 X3 x
           have i₂ := b3e1109 x X0 X1 X0 (M.op X2 X3)
           grind)
        | exact superpose b3e1109 b3e1248
        | exact resolve b3e1248 b3e1109
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1109 b3e1248
      have b3e1257 : ∀ X2 X3 X4 : G, (M.op X3 X4) = (M.op X3 (M.op (M.op X2 X2) X4)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b3e1252 x X2 X3 X4
           have i₂ := b3e1213 x X4 X3 (M.op X2 X2)
           grind)
        | exact superpose b3e1213 b3e1252
        | exact resolve b3e1252 b3e1213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1213 b3e1252
      have b3e1259 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1254 X0 X1 X2 X3
           have i₂ := b3e1170 X2 X3 X0 X0
           grind)
        | (have i₁ := b3e1254 X0 X1 (M.op X0 X3) X1
           have i₂ := b3e1170 X0 X1 (M.op X0 X0) X3
           grind)
        | exact superpose b3e1170 b3e1254
        | exact resolve b3e1254 b3e1170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1170 b3e1254
      have b3e1261 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X2 X1) X3) := by
        intro X1 X2 X3
        first
        | (have i₁ := b3e1259 x X1 X2 X3
           have i₂ := b3e10 X2 X3 x
           grind)
        | exact superpose b3e10 b3e1259
        | exact resolve b3e1259 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1259
      have b3e1306 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 X0 X2 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)
           have i₂ := b3e115 X3 X4 X0 X1
           grind)
        | exact superpose b3e115 b3e10
        | exact resolve b3e10 b3e115
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1348 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1306 X0 X1 X2 X3 X4
           have i₂ := b3e1193 X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X1 X2
           grind)
        | (have i₁ := b3e1306 X0 X1 X2 X3 X4
           have i₂ := b3e1193 X0 X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X2
           grind)
        | exact superpose b3e1193 b3e1306
        | exact resolve b3e1306 b3e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1306
      have b3e1385 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X1 (M.op (M.op X3 X4) (M.op X3 X4))) (M.op X0 X2))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1348 X0 X1 X2 X3 X4
           have i₂ := b3e144 X1 X0 X2 X1 (M.op X3 X4) (M.op X3 X4)
           grind)
        | (have i₁ := b3e1348 X0 x (M.op X1 X2) X3 X4
           have i₂ := b3e144 X0 X1 X2 x (M.op (M.op X3 X4) (M.op X3 X4)) x
           grind)
        | exact superpose b3e144 b3e1348
        | exact resolve b3e1348 b3e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1348
      have b3e1415 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) (M.op X1 (M.op X0 X2)))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1385 X0 X1 X2 X3 X4
           have i₂ := b3e144 (M.op X3 X4) X1 (M.op X0 X2) X1 X3 X4
           grind)
        | (have i₁ := b3e1385 X1 X0 X2 X3 X4
           have i₂ := b3e144 X0 X1 X2 X0 (M.op X3 X4) (M.op X3 X4)
           grind)
        | exact superpose b3e144 b3e1385
        | exact resolve b3e1385 b3e144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e144 b3e1385
      have b3e1441 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X1 (M.op X0 X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1415 X0 X1 X2 x x
           have i₂ := b3e1257 (M.op x x) X1 (M.op X1 (M.op X0 X2))
           grind)
        | (have i₁ := b3e1415 X0 x X2 x x
           have i₂ := b3e1257 X2 x (M.op (M.op (M.op x x) (M.op x x)) (M.op x (M.op X0 X2)))
           grind)
        | exact superpose b3e1257 b3e1415
        | exact resolve b3e1415 b3e1257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1415
      have b3e1607 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e219 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e219
        | (have j0 := b3e219 (τ X0)
           grind)
        | exact resolve b3e219 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e1613 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e1607 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1607
        | (have j0 := b3e1607 X0
           grind)
        | exact resolve b3e1607 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1607
      have b3e1620 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e1613 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1613
        | (have j0 := b3e1613 X0
           grind)
        | exact resolve b3e1613 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1613
      have b3e2083 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e70 x y X0
           grind)
        | exact superpose b3e70 b3e16
        | (have j1 := b3e70 x x X0
           grind)
        | exact resolve b3e16 b3e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e70
      have b3e3460 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e1441 (M.op (M.op X2 X3) (M.op X2 X3)) X0 X1
           have i₂ := b3e115 X2 X3 X0 X1
           grind)
        | exact superpose b3e115 b3e1441
        | exact resolve b3e1441 b3e115
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e115 b3e1441
      have b3e3540 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X3 (M.op X2 (M.op X2 X3))) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e3460 X0 X1 X2 X3
           have i₂ := b3e1241 X3 X2 (M.op X2 X3) X1
           grind)
        | exact superpose b3e1241 b3e3460
        | exact resolve b3e3460 b3e1241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1241 b3e3460
      have b3e3556 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 (M.op X2 X3)) (M.op X3 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e3540 X0 X1 X2 X3
           have i₂ := b3e1261 (M.op X2 (M.op X2 X3)) X3 X1
           grind)
        | exact superpose b3e1261 b3e3540
        | exact resolve b3e3540 b3e1261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3540
      have b3e3568 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op (M.op X2 (M.op X2 X3)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e3556 X0 X1 X2 X3
           have i₂ := b3e1190 X3 X1 (M.op X2 (M.op X2 X3))
           grind)
        | (have i₁ := b3e3556 X0 X1 X2 X3
           have i₂ := b3e1190 (M.op X2 (M.op X2 X3)) X1 X3
           grind)
        | exact superpose b3e1190 b3e3556
        | exact resolve b3e3556 b3e1190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1190 b3e3556
      have b3e3578 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e3568 X0 X1 x X3
           have i₂ := b3e1149 X3 x X3 X1
           grind)
        | (have i₁ := b3e3568 X0 X1 x (M.op X3 X1)
           have i₂ := b3e1149 X1 x X3 (M.op (M.op x (M.op x (M.op X3 X1))) X1)
           grind)
        | exact superpose b3e1149 b3e3568
        | exact resolve b3e3568 b3e1149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3568
      have b3e3585 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e3578 X0 X1 X3
           have i₂ := b3e1261 X3 X3 X1
           grind)
        | exact superpose b3e1261 b3e3578
        | exact resolve b3e3578 b3e1261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3578
      have b3e17667 : ∀ X0 X1 : G, (M.op (σ y) (σ (M.op y X0))) = (M.op X1 (M.op X1 (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e3585 X1 (σ X0) (σ y)
           have i₂ := b3e531 X0
           grind)
        | exact superpose b3e531 b3e3585
        | exact resolve b3e3585 b3e531
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e531 b3e3585
      have b3e17991 : ∀ X0 X1 : G, (σ (k (M.op y X0) y)) = (M.op X1 (M.op X1 (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e17667 X0 X1
           have i₂ := b3e37 (M.op y X0)
           grind)
        | exact superpose b3e37 b3e17667
        | exact resolve b3e17667 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37 b3e17667
      have b3e18166 : ∀ X0 X1 : G, (σ (M.op y (M.op y X0))) = (M.op X1 (M.op X1 (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e17991 X0 X1
           have i₂ := b3e121 (M.op y X0)
           grind)
        | exact superpose b3e121 b3e17991
        | exact resolve b3e17991 b3e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e121 b3e17991
      have b3e130692 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e2083 X0
           have i₂ := b3e662 y x
           grind)
        | exact superpose b3e662 b3e2083
        | (have j0 := b3e2083 X0
           have j1 := b3e662 X0 x
           grind)
        | (have r₁ := b3e2083 X0
           have r₂ := b3e662 y x
           grind)
        | exact resolve b3e2083 b3e662
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e662 b3e2083
      have b3e130694 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e130692 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e130692
      have b3e130725 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e496 (σ x) X0
           have i₂ := b3e130694 (σ x)
           grind)
        | exact superpose b3e130694 b3e496
        | (have j0 := b3e496 (σ x) X0
           grind)
        | exact resolve b3e496 b3e130694
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e496 b3e130694
      have b3e130765 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e130725 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e130725
      have b3e130783 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e130765 X0
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e130765
        | exact resolve b3e130765 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e130765
      have b3e130801 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e130783 X0
           have j1 := b3e13 X0 x
           grind)
        | (have r₁ := b3e130783 X0
           have r₂ := b3e13 X0 x
           grind)
        | exact resolve b3e130783 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e130783
      have b3e130998 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e219 x
           have i₂ := b3e130801 x
           grind)
        | exact superpose b3e130801 b3e219
        | (have j0 := b3e219 x
           grind)
        | exact resolve b3e219 b3e130801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e219
      have b3e131002 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e1620 x
           have i₂ := b3e130801 x
           grind)
        | exact superpose b3e130801 b3e1620
        | (have j0 := b3e1620 x
           grind)
        | (have r₁ := b3e1620 x
           have r₂ := b3e130801 x
           grind)
        | exact resolve b3e1620 b3e130801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1620 b3e130801
      have b3e131046 : x = (M.op x x) := by grind
      clear b3e131002
      have b3e131050 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e130998
      have b3e131774 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op (M.op x X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e21 x X1 x X0
           have i₂ := b3e131046
           grind)
        | exact superpose b3e131046 b3e21
        | exact resolve b3e21 b3e131046
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131046
      have b3e131899 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x (M.op x X1)) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e131774 X0 X1
           have i₂ := b3e1193 x (M.op x X1) X1 X0
           grind)
        | (have i₁ := b3e131774 X0 X1
           have i₂ := b3e1193 x X1 (M.op x X1) X0
           grind)
        | exact superpose b3e1193 b3e131774
        | exact resolve b3e131774 b3e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131774
      have b3e131928 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e131899 X0 X1
           have i₂ := b3e1149 X1 x X1 X0
           grind)
        | (have i₁ := b3e131899 X0 (M.op x X1)
           have i₂ := b3e1149 X1 x x (M.op (M.op x (M.op x (M.op x X1))) X0)
           grind)
        | exact superpose b3e1149 b3e131899
        | exact resolve b3e131899 b3e1149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131899
      have b3e131948 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e131928 X0 X1
           have i₂ := b3e1261 X1 X1 X0
           grind)
        | exact superpose b3e1261 b3e131928
        | exact resolve b3e131928 b3e1261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131928
      have b3e134007 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e1257 (σ x) X0 X1
           have i₂ := b3e131050
           grind)
        | exact superpose b3e131050 b3e1257
        | exact resolve b3e1257 b3e131050
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1257
      have b3e134026 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X1) (M.op (M.op (σ x) X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e21 (σ x) X1 (σ x) X0
           have i₂ := b3e131050
           grind)
        | exact superpose b3e131050 b3e21
        | exact resolve b3e21 b3e131050
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21 b3e131050
      have b3e134152 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op X1 (M.op (M.op (σ x) (M.op (σ x) X1)) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e134026 X0 X1
           have i₂ := b3e1193 (σ x) (M.op (σ x) X1) X1 X0
           grind)
        | (have i₁ := b3e134026 X0 X1
           have i₂ := b3e1193 (σ x) X1 (M.op (σ x) X1) X0
           grind)
        | exact superpose b3e1193 b3e134026
        | exact resolve b3e134026 b3e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1193 b3e134026
      have b3e134197 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e134152 X0 X1
           have i₂ := b3e1149 X1 (σ x) X1 X0
           grind)
        | (have i₁ := b3e134152 X0 (M.op x X1)
           have i₂ := b3e1149 X1 x x (M.op (M.op (σ x) (M.op (σ x) (M.op x X1))) X0)
           grind)
        | exact superpose b3e1149 b3e134152
        | exact resolve b3e134152 b3e1149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1149 b3e134152
      have b3e134219 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e134197 X0 X1
           have i₂ := b3e1261 X1 X1 X0
           grind)
        | exact superpose b3e1261 b3e134197
        | exact resolve b3e134197 b3e1261
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1261 b3e134197
      have b3e134234 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e134219 X0 x
           have i₂ := b3e131948 X0 x
           grind)
        | exact superpose b3e131948 b3e134219
        | exact resolve b3e134219 b3e131948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e134219
      have b3e135089 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e134234 (σ y)
           grind)
        | exact superpose b3e134234 b3e16
        | exact resolve b3e16 b3e134234
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e135254 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op x (M.op (σ x) (σ X0))) := by
        intro X0
        first
        | (have i₁ := b3e18166 X0 (σ x)
           have i₂ := b3e134234 (M.op (σ x) (σ X0))
           grind)
        | exact superpose b3e134234 b3e18166
        | exact resolve b3e18166 b3e134234
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e18166 b3e134234
      have b3e135299 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e135254 X0
           have i₂ := b3e134007 x (σ X0)
           grind)
        | exact superpose b3e134007 b3e135254
        | exact resolve b3e135254 b3e134007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e134007 b3e135254
      have b3e135494 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e135299 X0
           have i₂ := b3e131948 X0 y
           grind)
        | exact superpose b3e131948 b3e135299
        | exact resolve b3e135299 b3e131948
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131948 b3e135299
      have b3e143240 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e135089
           have i₂ := b3e135494 y
           grind)
        | exact superpose b3e135494 b3e135089
        | (have r₁ := b3e135089
           have r₂ := b3e135494 y
           grind)
        | exact resolve b3e135089 b3e135494
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e135089 b3e135494
      have b3e143306 : False := by grind
      exact b3e143306

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation3591 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
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
      have b0e69 : False := by grind
      exact b0e69
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b4e32 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X3 (M.op (M.op X0 X2) X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (M.op (M.op X0 y) X1)
               have i₂ := b4e13 X0 X1 y
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b4e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e47 X0 X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e47
            | (have j0 := b4e47 X0 X1
               grind)
            | exact resolve b4e47 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e59 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e38 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y
               have i₂ := b4e38 (M.op X0 y) X1
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e161 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op (M.op (M.op y X0) X2) (M.op (M.op y X2) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 y X2 (M.op y X0) X1
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e34
            | exact resolve b4e34 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e173 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op (σ X0) X1) (σ X0)) (M.op (σ (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 (σ X0) (σ X0) X1 X2
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e34
            | exact resolve b4e34 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e177 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op y X1) (M.op y X0)) (M.op (M.op y X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 y (M.op y X0) X1 X2
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e34
            | exact resolve b4e34 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e182 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e34 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
               have i₂ := b4e13 X0 X1 (M.op X3 X4)
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e186 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
               have i₂ := b4e34 X2 X3 X0 X1
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e187 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op (M.op X2 y) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e64 (M.op X2 X0) (M.op (M.op X2 y) X1)
               have i₂ := b4e34 X2 y X0 X1
               grind)
            | exact superpose b4e34 b4e64
            | exact resolve b4e64 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e192 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e187 X0 X1 X2
               have i₂ := b4e64 X2 X1
               grind)
            | exact superpose b4e64 b4e187
            | exact resolve b4e187 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64 b4e187
          have b4e198 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op (M.op y X0) (M.op y (M.op y X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e177 X0 X1 X2
               have i₂ := b4e182 (M.op y X0) X2 X1 y (M.op y X0)
               grind)
            | exact superpose b4e182 b4e177
            | exact resolve b4e177 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177
          have b4e202 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e173 X0 X1 X2
               have i₂ := b4e182 (σ (M.op X0 X0)) X2 X1 (σ X0) (σ X0)
               grind)
            | exact superpose b4e182 b4e173
            | exact resolve b4e173 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173 b4e182
          have b4e213 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e161 X0 X1 x
               have i₂ := b4e34 y x X0 X1
               grind)
            | exact superpose b4e34 b4e161
            | exact resolve b4e161 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e161
          have b4e222 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 (M.op y X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e198 X0 X1 X2
               have i₂ := b4e192 X0 (M.op y X0) y
               grind)
            | exact superpose b4e192 b4e198
            | exact resolve b4e198 b4e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e198
          have b4e225 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e202 X0 X1 X2
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e202
            | exact resolve b4e202 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e202
          have b4e237 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e225 X0 X1 X2
               have i₂ := b4e30 (M.op X0 X0)
               grind)
            | exact superpose b4e30 b4e225
            | exact resolve b4e225 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e225
          have b4e243 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e237 X0 X1 X2
               have i₂ := b4e192 X0 X0 X0
               grind)
            | exact superpose b4e192 b4e237
            | exact resolve b4e237 b4e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e192 b4e237
          have b4e250 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X1 X0
               have i₂ := b4e213 X0 X1
               grind)
            | exact superpose b4e213 b4e13
            | exact resolve b4e13 b4e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e704 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e54 x y
               grind)
            | exact superpose b4e54 b4e20
            | (have j1 := b4e54 x (M.op x x)
               grind)
            | exact resolve b4e20 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e728 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e704
               have r₂ := b4e23
               grind)
            | exact resolve b4e704 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e704
          have b4e1659 : ∀ X0 X1 : G, (M.op y X0) = (M.op (σ (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 (σ (M.op X1 X1)) X0
               have i₂ := b4e243 X1 y X0
               grind)
            | exact superpose b4e243 b4e38
            | exact resolve b4e38 b4e243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e243
          have b4e3313 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e222 X0 (M.op X0 X1) X2
               have i₂ := b4e186 X1 X2 X0 (M.op y X0)
               grind)
            | exact superpose b4e186 b4e222
            | exact resolve b4e222 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186 b4e222
          have b4e3337 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e3313 X0 X1 X2
               have i₂ := b4e213 X0 (M.op X1 X2)
               grind)
            | exact superpose b4e213 b4e3313
            | exact resolve b4e3313 b4e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e213 b4e3313
          have b4e4065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b4e728
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e728
            | (have j1 := b4e18 (M.op x x) x
               grind)
            | (have r₁ := b4e728
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e728
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e728 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e728
          have b4e4066 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b4e4065
          have b4e4068 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b4e4066
               have r₂ := b4e21
               grind)
            | exact resolve b4e4066 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4066
          have b4e53250 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e4068
               grind)
            | exact superpose b4e4068 b4e14
            | exact resolve b4e14 b4e4068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4068
          have b4e53297 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e53250
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e53250
            | exact resolve b4e53250 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53250
          have b4e53298 : x = (M.op x x) := by grind
          clear b4e53297
          have b4e53915 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e1659 X0 x
               have i₂ := b4e53298
               grind)
            | exact superpose b4e53298 b4e1659
            | exact resolve b4e1659 b4e53298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1659
          have b4e53957 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e3337 x x X0
               have i₂ := b4e53298
               grind)
            | exact superpose b4e53298 b4e3337
            | exact resolve b4e3337 b4e53298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3337 b4e53298
          have b4e53960 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e53957 X0
               have i₂ := b4e250 x X0
               grind)
            | exact superpose b4e250 b4e53957
            | exact resolve b4e53957 b4e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e250 b4e53957
          have b4e58818 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e53915 (σ y)
               grind)
            | exact superpose b4e53915 b4e20
            | exact resolve b4e20 b4e53915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53915
          have b4e59063 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e58818
               have i₂ := b4e59
               grind)
            | exact superpose b4e59 b4e58818
            | exact resolve b4e58818 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59 b4e58818
          have b4e59140 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e59063
               have i₂ := b4e53960 y
               grind)
            | exact superpose b4e53960 b4e59063
            | exact resolve b4e59063 b4e53960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53960 b4e59063
          have b4e59187 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e59140
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e59140
            | exact resolve b4e59140 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59140
          have b4e59188 : False := by grind
          exact b4e59188
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b5e103 : (σ y) ≠ (σ (M.op y y)) := by
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
          have b5e108 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e103
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e103
            | exact resolve b5e103 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e109 : False := by grind
          exact b5e109
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b7e70 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e85 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e14
            | exact resolve b7e14 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e86 : y = (M.op y y) := by
            first
            | (have i₁ := b7e85
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e85
            | exact resolve b7e85 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e90 : False := by grind
          exact b7e90
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
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
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op (M.op X0 X2) X1)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b8e38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e39 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e35 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e35
            | exact resolve b8e35 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e40 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e39
          have b8e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e59 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
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
          have b8e60 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b8e59 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e54 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e54
            | (have j0 := b8e54 X0 X1
               grind)
            | exact resolve b8e54 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e68 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e111 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e38 X0 y
               have i₂ := b8e60 X0
               grind)
            | exact superpose b8e60 b8e38
            | (have j1 := b8e60 X0
               grind)
            | exact resolve b8e38 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e60
          have b8e288 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x (M.op x x)
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e310 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e288
               have r₂ := b8e23
               grind)
            | exact resolve b8e288 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e288
          have b8e463 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X2) = (M.op (M.op (M.op (σ X0) X1) X3) (M.op (M.op (σ X0) X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32 (σ X0) X3 (M.op (σ (M.op X0 X0)) X1) X2
               have i₂ := b8e69 X0 X1
               grind)
            | exact superpose b8e69 b8e32
            | exact resolve b8e32 b8e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e470 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e463 X0 X1 X2 x
               have i₂ := b8e32 (σ X0) x X1 X2
               grind)
            | exact superpose b8e32 b8e463
            | exact resolve b8e463 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e463
          have b8e487 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e470 (τ X0) X1 X2
               have i₂ := b8e40 X0
               grind)
            | exact superpose b8e40 b8e470
            | exact resolve b8e470 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e470
          have b8e619 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X2 X2) X1 X0
               have i₂ := b8e487 X2 X0 X1
               grind)
            | exact superpose b8e487 b8e13
            | exact resolve b8e13 b8e487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e487
          have b8e3970 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e310
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e310
            | (have j1 := b8e18 (M.op x x) x
               grind)
            | (have r₁ := b8e310
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e310
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e310 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e310
          have b8e3971 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b8e3970
          have b8e3973 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b8e3971
               have r₂ := b8e21
               grind)
            | exact resolve b8e3971 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3971
          have b8e14045 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e3973
               grind)
            | exact superpose b8e3973 b8e14
            | exact resolve b8e14 b8e3973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3973
          have b8e14083 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14045
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e14045
            | exact resolve b8e14045 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14045
          have b8e14084 : x = (M.op x x) := by grind
          clear b8e14083
          have b8e16218 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b8e69 x X0
               have i₂ := b8e14084
               grind)
            | exact superpose b8e14084 b8e69
            | exact resolve b8e69 b8e14084
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e16225 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e619 X0 X1 x
               have i₂ := b8e14084
               grind)
            | exact superpose b8e14084 b8e619
            | exact resolve b8e619 b8e14084
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e619 b8e14084
          have b8e16282 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e16218 X0
               have i₂ := b8e16225 (σ x) X0
               grind)
            | exact superpose b8e16225 b8e16218
            | exact resolve b8e16218 b8e16225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16218
          have b8e24892 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e16282 (σ y)
               grind)
            | exact superpose b8e16282 b8e20
            | exact resolve b8e20 b8e16282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16282
          have b8e35306 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e16225 (σ X0) (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e16225
            | exact resolve b8e16225 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e134510 : (k (τ (σ (M.op y y))) y) = (τ (M.op x (σ y))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e111 (σ (M.op y y))
               have i₂ := b8e35306 y
               grind)
            | exact superpose b8e35306 b8e111
            | (have j0 := b8e111 (σ (M.op y y))
               grind)
            | exact resolve b8e111 b8e35306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111 b8e35306
          have b8e134591 : (k (τ (σ (M.op y y))) y) = (τ (M.op x (σ y))) := by
            first
            | (have r₁ := b8e134510
               have r₂ := b8e68
               grind)
            | exact resolve b8e134510 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68 b8e134510
          have b8e134617 : (k (M.op y y) y) = (τ (M.op x (σ y))) := by
            first
            | (have i₁ := b8e134591
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e134591
            | exact resolve b8e134591 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134591
          have b8e134644 : (M.op x (σ y)) = (σ (k (M.op y y) y)) := by
            first
            | (have i₁ := b8e15 (M.op x (σ y))
               have i₂ := b8e134617
               grind)
            | exact superpose b8e134617 b8e15
            | exact resolve b8e15 b8e134617
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134617
          have b8e134781 : (M.op x (σ y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e134644
               have i₂ := b8e18 (M.op y y) y
               grind)
            | exact superpose b8e18 b8e134644
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | exact resolve b8e134644 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134644
          have b8e134830 : (M.op x (σ y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) := by grind
          clear b8e134781
          have b8e134861 : (M.op x (σ y)) = (σ (M.op y (M.op y y))) := by
            first
            | (have r₁ := b8e134830
               have r₂ := b8e22
               grind)
            | exact resolve b8e134830 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134830
          have b8e134881 : (σ (M.op x y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e134861
               have i₂ := b8e16225 y y
               grind)
            | exact superpose b8e16225 b8e134861
            | exact resolve b8e134861 b8e16225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16225 b8e134861
          have b8e134901 : False := by grind
          exact b8e134901

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pyy_y_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e26 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b1e12 y x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b1e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
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
        have b1e36 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e29 x y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e29
          | exact resolve b1e29 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 x
             have i₂ := b1e29 (M.op X0 X1) X0 x
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : x ≠ x ∨ (k x y) = (M.op y y) := by
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
        have b1e50 : ∀ X0 : G, (M.op y x) ≠ X0 ∨ (k X0 (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 (M.op x x)
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e15
          | (have j0 := b1e15 X0 (M.op x x)
             grind)
          | (have r₁ := b1e15 (M.op y x) (M.op x x)
             have r₂ := b1e26 (M.op y x)
             grind)
          | exact resolve b1e15 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : (k x y) = (M.op y y) := by grind
        clear b1e48
        have b1e56 : ∀ X0 : G, x ≠ X0 ∨ (k X0 (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b1e50 X0
             have i₂ := b1e36 y
             grind)
          | exact superpose b1e36 b1e50
          | (have j0 := b1e50 X0
             grind)
          | (have r₁ := b1e50 x
             have r₂ := b1e36 y
             grind)
          | exact resolve b1e50 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e58 : ∀ X0 : G, (M.op y x) = (k X0 (M.op x x)) ∨ x ≠ X0 := by
          intro X0
          first
          | (have i₁ := b1e56 X0
             have i₂ := b1e26 (M.op x x)
             grind)
          | exact superpose b1e26 b1e56
          | (have j0 := b1e56 X0
             grind)
          | exact resolve b1e56 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e56
        have b1e60 : ∀ X0 : G, (M.op y x) = (k X0 x) ∨ x ≠ X0 := by
          intro X0
          first
          | (have i₁ := b1e58 X0
             have i₂ := b1e36 x
             grind)
          | exact superpose b1e36 b1e58
          | (have j0 := b1e58 X0
             grind)
          | (have r₁ := b1e58 (M.op X0 x)
             have r₂ := b1e36 X0
             grind)
          | exact resolve b1e58 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e60 X0
             have i₂ := b1e36 y
             grind)
          | exact superpose b1e36 b1e60
          | (have j0 := b1e60 X0
             grind)
          | (have r₁ := b1e60 (M.op X0 x)
             have r₂ := b1e36 X0
             grind)
          | exact resolve b1e60 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e73 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 x
             have i₂ := b1e36 X0
             grind)
          | exact superpose b1e36 b1e16
          | (have j0 := b1e16 X0 x
             grind)
          | exact resolve b1e16 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e79 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 ∨ (σ y) = (k X0 (σ y)) := by
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
        have b1e87 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e73 (k X0 x)
             have j1 := b1e61 (M.op x x)
             grind)
          | (have r₁ := b1e73 X0
             have r₂ := b1e61 X0
             grind)
          | (have r₁ := b1e73 x
             have r₂ := b1e61 x
             grind)
          | (have r₁ := b1e73 X0
             have r₂ := b1e61 (k X0 x)
             grind)
          | exact resolve b1e73 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e73
        have b1e95 : ∀ X0 : G, x = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e87 X0
             grind)
          | (have r₁ := b1e87 X0
             have r₂ := b1e36 x
             grind)
          | exact resolve b1e87 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e87
        have b1e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X1 X0
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e15 X1 X1
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X1 X0
             have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e15 (M.op X1 X1) X1
             have r₂ := b1e17 (M.op X1 X1) X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e116 X0 X1
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e116 X1 (k X0 X1)
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e116 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e116 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116
        have b1e143 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e24 X0 x
             have i₂ := b1e95 (τ X0)
             grind)
          | exact superpose b1e95 b1e24
          | exact resolve b1e24 b1e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e95
        have b1e532 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e136 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e136
        have b1e533 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e532 X0
             have i₂ := b1e43 X0 X0
             grind)
          | exact superpose b1e43 b1e532
          | (have j0 := b1e532 X0
             grind)
          | exact resolve b1e532 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e532
        have b1e534 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e533 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e533
        have b1e677 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e143 (M.op (σ x) (σ x))
             have i₂ := b1e534 (σ x)
             grind)
          | exact superpose b1e534 b1e143
          | exact resolve b1e143 b1e534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e143 b1e534
        have b1e774 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b1e79 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e777 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e774
             have r₂ := b1e21
             grind)
          | exact resolve b1e774 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774
        have b1e780 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e777
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e777
          | exact resolve b1e777 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e777
        have b1e782 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e780
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e780
          | exact resolve b1e780 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e780
        have b1e789 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e782
             grind)
          | exact superpose b1e782 b1e13
          | exact resolve b1e13 b1e782
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e782
        have b1e790 : y = (M.op y y) := by
          first
          | (have i₁ := b1e789
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e789
          | exact resolve b1e789 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e789
        have b1e839 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e29 y y x
             have i₂ := b1e790
             grind)
          | exact superpose b1e790 b1e29
          | exact resolve b1e29 b1e790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e790
        have b1e944 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e839 x
             grind)
          | exact superpose b1e839 b1e20
          | exact resolve b1e20 b1e839
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e839
        have b1e1098 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e944
             grind)
          | exact superpose b1e944 b1e21
          | exact resolve b1e21 b1e944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e944
        have b1e1113 : False := by grind
        exact b1e1113
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b2e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e28 X0 X1 x X3
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e40 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 x
             have i₂ := b2e29 (M.op X0 X1) X0 x
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : x ≠ x ∨ (k x y) = (M.op y y) := by
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
        have b2e48 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X2 (M.op X0 X1)
             have i₂ := b2e29 X0 X1 X2
             grind)
          | exact superpose b2e29 b2e15
          | (have j0 := b2e15 X2 (M.op X0 X1)
             grind)
          | (have r₁ := b2e15 (M.op X0 X1) (M.op X0 X1)
             have r₂ := b2e29 X0 X1 (M.op X0 X1)
             grind)
          | exact resolve b2e15 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : (k x y) = (M.op y y) := by grind
        clear b2e45
        have b2e50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e48 X0 X1 X2
             have i₂ := b2e29 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e29 b2e48
          | (have j0 := b2e48 X0 X1 X2
             grind)
          | (have r₁ := b2e48 X0 X1 (M.op x (M.op X0 X1))
             have r₂ := b2e29 X0 X1 x
             grind)
          | (have r₁ := b2e48 x (M.op X0 X1) (M.op X0 X1)
             have r₂ := b2e29 X0 X1 x
             grind)
          | exact resolve b2e48 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e67 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 x (M.op X0 X1)
             have i₂ := b2e29 X0 X1 x
             grind)
          | exact superpose b2e29 b2e16
          | (have j0 := b2e16 X2 (M.op X0 X1)
             grind)
          | exact resolve b2e16 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e73 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e16 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e79 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e67 X0 X1 (k X2 (M.op X0 X1))
             have j1 := b2e50 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
             grind)
          | (have r₁ := b2e67 X0 X1 X2
             have r₂ := b2e50 X0 X1 X2
             grind)
          | (have r₁ := b2e67 X0 X1 (M.op X0 X1)
             have r₂ := b2e50 X0 X1 (M.op X0 X1)
             grind)
          | (have r₁ := b2e67 X0 X1 X2
             have r₂ := b2e50 X0 X1 (k X2 (M.op X0 X1))
             grind)
          | exact resolve b2e67 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e67
        have b2e87 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e79 X0 X1 X2
             grind)
          | (have r₁ := b2e79 X0 X1 X2
             have r₂ := b2e29 X0 X1 (M.op X0 X1)
             grind)
          | exact resolve b2e79 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e103 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e16 (M.op X1 X1) X1
             have r₂ := b2e17 (M.op X1 X1) X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e120 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
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
        have b2e121 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e123 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e105 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105
        have b2e126 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e123 X0 X1
             have j1 := b2e121 X1 X0
             grind)
          | (have r₁ := b2e123 X1 X0
             have r₂ := b2e121 X0 X1
             grind)
          | (have r₁ := b2e123 X0 (M.op X1 X1)
             have r₂ := b2e121 (M.op X0 X0) X1
             grind)
          | (have r₁ := b2e123 (M.op X1 X1) X1
             have r₂ := b2e121 (k X1 (M.op X1 X1)) X1
             grind)
          | exact resolve b2e123 b2e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e121 b2e123
        have b2e164 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 (τ X0)
             have i₂ := b2e73 (τ X0)
             grind)
          | exact superpose b2e73 b2e24
          | (have j1 := b2e73 (τ X0)
             grind)
          | exact resolve b2e24 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e165 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e164 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e164
          | (have j0 := b2e164 X0
             grind)
          | exact resolve b2e164 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e164
        have b2e350 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k (M.op X1 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (M.op X1 X0) X1
             have i₂ := b2e40 X1 X0
             grind)
          | exact superpose b2e40 b2e15
          | (have j0 := b2e15 (M.op X1 X0) X1
             grind)
          | (have r₁ := b2e15 (M.op X1 X1) X1
             have r₂ := b2e40 X1 X1
             grind)
          | exact resolve b2e15 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e404 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e24 X2 (M.op X0 X1)
             have i₂ := b2e87 X0 X1 (τ X2)
             grind)
          | exact superpose b2e87 b2e24
          | exact resolve b2e24 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e87
        have b2e405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e126 (σ X1) (σ X0)
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e126
          | (have j0 := b2e126 (σ X1) (σ X0)
             grind)
          | exact resolve b2e126 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126
        have b2e662 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e120 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120
        have b2e663 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e662
             have r₂ := b2e21
             grind)
          | exact resolve b2e662 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e662
        have b2e665 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e663
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e663
          | exact resolve b2e663 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e663
        have b2e667 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e665
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e665
          | exact resolve b2e665 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e665
        have b2e673 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e667
             grind)
          | exact superpose b2e667 b2e21
          | exact resolve b2e21 b2e667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e722 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e103 X0 y
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e103 y y
             grind)
          | exact superpose b2e103 b2e22
          | (have j1 := b2e103 X0 y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e103 x y
             grind)
          | exact resolve b2e22 b2e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103
        have b2e768 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e722 X0
             have i₂ := b2e667
             grind)
          | exact superpose b2e667 b2e722
          | (have j0 := b2e722 X0
             grind)
          | exact resolve b2e722 b2e667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e667 b2e722
        have b2e1279 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e404 (τ X0) (τ X0) x
             have i₂ := b2e165 X0
             grind)
          | exact superpose b2e165 b2e404
          | (have j1 := b2e165 X0
             grind)
          | exact resolve b2e404 b2e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e165 b2e404
        have b2e1304 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1279 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1279
          | (have j0 := b2e1279 X0 X1
             grind)
          | exact resolve b2e1279 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1279
        have b2e1359 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e1304 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1304
        have b2e1360 : ∀ X0 : G, (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e1359 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1359
        have b2e3321 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e405 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e405
        have b2e5434 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e350 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e350
        have b2e39545 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e3321 (M.op X0 X0) X0
             have i₂ := b2e5434 X0
             grind)
          | exact superpose b2e5434 b2e3321
          | (have j0 := b2e3321 (M.op X0 X0) X0
             grind)
          | exact resolve b2e3321 b2e5434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3321
        have b2e39578 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e39545 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39545
        have b2e40092 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e15 (σ (M.op X0 X0)) (σ X0)
             have i₂ := b2e39578 X0
             grind)
          | exact superpose b2e39578 b2e15
          | (have j0 := b2e15 (σ (M.op X0 X0)) (σ X0)
             have j1 := b2e39578 X0
             grind)
          | (have r₁ := b2e15 (σ (M.op X0 X0)) (σ X0)
             have r₂ := b2e39578 X0
             grind)
          | exact resolve b2e15 b2e39578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39578
        have b2e40134 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e40092 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40092
        have b2e40181 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e40134 X0
             have i₂ := b2e18 (M.op X0 X0) X0
             grind)
          | exact superpose b2e18 b2e40134
          | (have j0 := b2e40134 X0
             grind)
          | exact resolve b2e40134 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40134
        have b2e40278 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e40181 X0
             have i₂ := b2e5434 X0
             grind)
          | exact superpose b2e5434 b2e40181
          | (have j0 := b2e40181 X0
             grind)
          | exact resolve b2e40181 b2e5434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5434 b2e40181
        have b2e41136 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e768 y
             have i₂ := b2e40278 y
             grind)
          | exact superpose b2e40278 b2e768
          | (have j1 := b2e40278 y
             grind)
          | (have r₁ := b2e768 y
             have r₂ := b2e40278 y
             grind)
          | exact resolve b2e768 b2e40278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e768 b2e40278
        have b2e41281 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
        clear b2e41136
        have b2e41282 : (σ (M.op y y)) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
        clear b2e41281
        have b2e41367 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e41282
             have i₂ := b2e1360 y
             grind)
          | exact superpose b2e1360 b2e41282
          | exact resolve b2e41282 b2e1360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1360 b2e41282
        have b2e41368 : (σ y) = (σ (M.op y y)) := by grind
        clear b2e41367
        have b2e41691 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e673
             have i₂ := b2e41368
             grind)
          | exact superpose b2e41368 b2e673
          | exact resolve b2e673 b2e41368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e673
        have b2e41705 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b2e13 (M.op y y)
             have i₂ := b2e41368
             grind)
          | exact superpose b2e41368 b2e13
          | exact resolve b2e13 b2e41368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41368
        have b2e41842 : y = (M.op y y) := by
          first
          | (have i₁ := b2e41705
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e41705
          | exact resolve b2e41705 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41705
        have b2e43185 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e29 y y x
             have i₂ := b2e41842
             grind)
          | exact superpose b2e41842 b2e29
          | exact resolve b2e29 b2e41842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e41842
        have b2e43607 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e43185 x
             grind)
          | exact superpose b2e43185 b2e20
          | exact resolve b2e20 b2e43185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43185
        have b2e43742 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e41691
             have i₂ := b2e43607
             grind)
          | exact superpose b2e43607 b2e41691
          | exact resolve b2e41691 b2e43607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41691 b2e43607
        have b2e43745 : False := by grind
        exact b2e43745
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b3e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e29 X0 X1 x X3
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e29
          | exact resolve b3e29 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e32 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e30 (σ x) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e30
          | exact resolve b3e30 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 x
             have i₂ := b3e30 (M.op X0 X1) X0 x
             grind)
          | exact superpose b3e30 b3e12
          | exact resolve b3e12 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e44 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e41
        have b3e47 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e50 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ x) (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ x)
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e15
          | (have j0 := b3e15 X0 (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ x)
             have r₂ := b3e32 (σ x)
             grind)
          | exact resolve b3e15 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (σ x) ≠ X0 := by
          intro X0
          first
          | (have i₁ := b3e50 X0
             have i₂ := b3e32 (σ x)
             grind)
          | exact superpose b3e32 b3e50
          | (have j0 := b3e50 X0
             grind)
          | (have r₁ := b3e50 (M.op X0 (σ x))
             have r₂ := b3e32 X0
             grind)
          | exact resolve b3e50 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e58 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = X0 ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 (σ x)
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e16
          | (have j0 := b3e16 X0 (σ x)
             grind)
          | exact resolve b3e16 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 y) = X0 ∨ y = (k X0 y) := by
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
        have b3e68 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e58 (k X0 (σ x))
             have j1 := b3e53 X0
             grind)
          | (have r₁ := b3e58 X0
             have r₂ := b3e53 X0
             grind)
          | (have r₁ := b3e58 (σ x)
             have r₂ := b3e53 (σ x)
             grind)
          | (have r₁ := b3e58 X0
             have r₂ := b3e53 (k X0 (σ x))
             grind)
          | exact resolve b3e58 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e58
        have b3e74 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e68 X0
             grind)
          | (have r₁ := b3e68 X0
             have r₂ := b3e32 (σ x)
             grind)
          | exact resolve b3e68 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e68
        have b3e81 : ∀ X0 : G, (σ x) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e74 (σ X0)
             grind)
          | exact superpose b3e74 b3e18
          | exact resolve b3e18 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e15 X1 X1
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e15 (M.op X1 X1) X1
             have r₂ := b3e17 (M.op X1 X1) X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e94 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e94 X1 (k X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e94 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e94 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e169 : ∀ X0 : G, (σ (k x y)) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e30 (σ y) (σ y) x
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e30
          | exact resolve b3e30 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e47
        have b3e527 : x = (M.op x y) ∨ y = (k x y) := by
          first
          | (have j0 := b3e59 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e529 : y = (k x y) := by
          first
          | (have r₁ := b3e527
             have r₂ := b3e20
             grind)
          | exact resolve b3e527 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e527
        have b3e621 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b3e113 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e113
        have b3e622 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b3e621 X0
             have i₂ := b3e36 X0 X0
             grind)
          | exact superpose b3e36 b3e621
          | (have j0 := b3e621 X0
             grind)
          | exact resolve b3e621 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e621
        have b3e623 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b3e622 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e622
        have b3e665 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e81 (M.op x x)
             have i₂ := b3e623 x
             grind)
          | exact superpose b3e623 b3e81
          | exact resolve b3e81 b3e623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e623
        have b3e1523 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e169 X0
             have i₂ := b3e529
             grind)
          | exact superpose b3e529 b3e169
          | exact resolve b3e169 b3e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e169 b3e529
        have b3e1598 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e1523 (σ x)
             grind)
          | exact superpose b3e1523 b3e22
          | exact resolve b3e22 b3e1523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1523
        have b3e1668 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1598
             grind)
          | exact superpose b3e1598 b3e13
          | exact resolve b3e13 b3e1598
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1598
        have b3e1683 : x = y := by
          first
          | (have i₁ := b3e1668
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1668
          | exact resolve b3e1668 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1668
        have b3e1722 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e1683
             grind)
          | exact superpose b3e1683 b3e23
          | exact resolve b3e23 b3e1683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1683
        have b3e1737 : False := by grind
        exact b3e1737
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
          have b4e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b4e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e33 X0 X1 x X3
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 x
               have i₂ := b4e34 (M.op X0 X1) X0 x
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e61 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (k X2 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X2 (M.op X0 X1)
               have i₂ := b4e34 X0 X1 X2
               grind)
            | exact superpose b4e34 b4e16
            | (have j0 := b4e16 X2 (M.op X0 X1)
               grind)
            | (have r₁ := b4e16 (M.op X0 X1) (M.op X0 X1)
               have r₂ := b4e34 X0 X1 (M.op X0 X1)
               grind)
            | exact resolve b4e16 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e61 X0 X1 X2
               have i₂ := b4e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e34 b4e61
            | (have j0 := b4e61 X0 X1 X2
               grind)
            | (have r₁ := b4e61 X0 X1 (M.op x (M.op X0 X1))
               have r₂ := b4e34 X0 X1 x
               grind)
            | (have r₁ := b4e61 x (M.op X0 X1) (M.op X0 X1)
               have r₂ := b4e34 X0 X1 x
               grind)
            | exact resolve b4e61 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e76 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 x (M.op X0 X1)
               have i₂ := b4e34 X0 X1 x
               grind)
            | exact superpose b4e34 b4e17
            | (have j0 := b4e17 X2 (M.op X0 X1)
               grind)
            | exact resolve b4e17 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e90 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e76 X0 X1 (k X2 (M.op X0 X1))
               have j1 := b4e65 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               grind)
            | (have r₁ := b4e76 X0 X1 X2
               have r₂ := b4e65 X0 X1 X2
               grind)
            | (have r₁ := b4e76 X0 X1 (M.op X0 X1)
               have r₂ := b4e65 X0 X1 (M.op X0 X1)
               grind)
            | (have r₁ := b4e76 X0 X1 X2
               have r₂ := b4e65 X0 X1 (k X2 (M.op X0 X1))
               grind)
            | exact resolve b4e76 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65 b4e76
          have b4e95 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e90 X0 X1 X2
               grind)
            | (have r₁ := b4e90 X0 X1 X2
               have r₂ := b4e34 X0 X1 (M.op X0 X1)
               grind)
            | exact resolve b4e90 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 (M.op X1 X1) X1
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 (M.op X1 X1) X1
               have r₂ := b4e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e125 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e127 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e108 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108
          have b4e130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e109 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e109 X1 (k X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e109 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e109 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e131 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e127 X0 X1
               have j1 := b4e125 X1 X0
               grind)
            | (have r₁ := b4e127 X1 X0
               have r₂ := b4e125 X0 X1
               grind)
            | (have r₁ := b4e127 X0 (M.op X1 X1)
               have r₂ := b4e125 (M.op X0 X0) X1
               grind)
            | (have r₁ := b4e127 (M.op X1 X1) X1
               have r₂ := b4e125 (k X1 (M.op X1 X1)) X1
               grind)
            | exact resolve b4e127 b4e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125 b4e127
          have b4e144 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29 X2 (M.op X0 X1)
               have i₂ := b4e95 X0 X1 (τ X2)
               grind)
            | exact superpose b4e95 b4e29
            | exact resolve b4e29 b4e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e95
          have b4e484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e131 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e131
            | (have j0 := b4e131 (σ X1) (σ X0)
               grind)
            | exact resolve b4e131 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131
          have b4e530 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b4e130 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e531 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b4e530 X0
               have i₂ := b4e39 X0 X0
               grind)
            | exact superpose b4e39 b4e530
            | (have j0 := b4e530 X0
               grind)
            | exact resolve b4e530 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e530
          have b4e532 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b4e531 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e531
          have b4e557 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e144 X0 X1 (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))
               have i₂ := b4e532 (σ (M.op X0 X1))
               grind)
            | exact superpose b4e532 b4e144
            | exact resolve b4e144 b4e532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144
          have b4e1653 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
               have i₂ := b4e557 X0 X1
               grind)
            | exact superpose b4e557 b4e34
            | exact resolve b4e34 b4e557
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e557
          have b4e3922 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e484 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e484
          have b4e26200 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e3922 (M.op X0 X0) X0
               have i₂ := b4e532 X0
               grind)
            | exact superpose b4e532 b4e3922
            | (have j0 := b4e3922 (M.op X0 X0) X0
               grind)
            | exact resolve b4e3922 b4e532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3922
          have b4e26240 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b4e26200 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26200
          have b4e26564 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e16 (σ (M.op X0 X0)) (σ X0)
               have i₂ := b4e26240 X0
               grind)
            | exact superpose b4e26240 b4e16
            | (have j0 := b4e16 (σ (M.op X0 X0)) (σ X0)
               have j1 := b4e26240 X0
               grind)
            | (have r₁ := b4e16 (σ (M.op X0 X0)) (σ X0)
               have r₂ := b4e26240 X0
               grind)
            | exact resolve b4e16 b4e26240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26240
          have b4e26601 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b4e26564 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26564
          have b4e26631 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e26601 X0
               have i₂ := b4e19 (M.op X0 X0) X0
               grind)
            | exact superpose b4e19 b4e26601
            | (have j0 := b4e26601 X0
               grind)
            | exact resolve b4e26601 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26601
          have b4e26704 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e26631 X0
               have i₂ := b4e532 X0
               grind)
            | exact superpose b4e532 b4e26631
            | (have j0 := b4e26631 X0
               grind)
            | exact resolve b4e26631 b4e532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e532 b4e26631
          have b4e26884 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e26704 y
               grind)
            | exact superpose b4e26704 b4e28
            | (have j1 := b4e26704 y
               grind)
            | (have r₁ := b4e28
               have r₂ := b4e26704 y
               grind)
            | exact resolve b4e28 b4e26704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26704
          have b4e27012 : (σ y) = (σ (M.op y y)) := by grind
          clear b4e26884
          have b4e27231 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e1653 y y x
               have i₂ := b4e27012
               grind)
            | exact superpose b4e27012 b4e1653
            | exact resolve b4e1653 b4e27012
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1653
          have b4e29346 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e27231 (σ y)
               grind)
            | exact superpose b4e27231 b4e28
            | exact resolve b4e28 b4e27231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e27231
          have b4e29513 : False := by grind
          exact b4e29513
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b5e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e31 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e68 : (M.op y y) ≠ (M.op y y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
          have b5e76 : x = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e68
          have b5e81 : y = (k x y) := by
            first
            | (have r₁ := b5e76
               have r₂ := b5e25
               grind)
            | exact resolve b5e76 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e76
          have b5e95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e606 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e95 x y
               grind)
            | exact superpose b5e95 b5e24
            | (have j1 := b5e95 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e95 x y
               grind)
            | exact resolve b5e24 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e653 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e606
          have b5e667 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e653
               have r₂ := b5e23
               grind)
            | exact resolve b5e653 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e653
          have b5e677 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e667
               have i₂ := b5e81
               grind)
            | exact superpose b5e81 b5e667
            | exact resolve b5e667 b5e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81 b5e667
          have b5e740 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e677
               grind)
            | exact superpose b5e677 b5e24
            | exact resolve b5e24 b5e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e750 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e32 (σ x) (σ y) x
               have i₂ := b5e677
               grind)
            | exact superpose b5e677 b5e32
            | exact resolve b5e32 b5e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e677
          have b5e762 : False := by grind
          exact b5e762
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 (M.op (M.op X1 X0) X1) X3
             have i₂ := b6e12 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e28 X0 X1 x X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e28
          | exact resolve b6e28 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 x
             have i₂ := b6e29 (M.op X0 X1) X0 x
             grind)
          | exact superpose b6e29 b6e12
          | exact resolve b6e12 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e41 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e38
        have b6e44 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b6e87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e16 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X1 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e16 (M.op X1 X1) X1
             have r₂ := b6e17 (M.op X1 X1) X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e102 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e104 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e87 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e104 X0 X1
             have j1 := b6e102 X1 X0
             grind)
          | (have r₁ := b6e104 X1 X0
             have r₂ := b6e102 X0 X1
             grind)
          | (have r₁ := b6e104 X0 (M.op X1 X1)
             have r₂ := b6e102 (M.op X0 X0) X1
             grind)
          | (have r₁ := b6e104 (M.op X1 X1) X1
             have r₂ := b6e102 (k X1 (M.op X1 X1)) X1
             grind)
          | exact resolve b6e104 b6e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102 b6e104
        have b6e158 : (σ (k x y)) = (M.op (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b6e34 (σ y) (σ y)
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e34
          | exact resolve b6e34 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e1971 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e158
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e158
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e158 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1976 : (σ (k x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ (k x y)) (σ y)
             have i₂ := b6e158
             grind)
          | exact superpose b6e158 b6e15
          | (have j0 := b6e15 (σ (k x y)) (σ y)
             grind)
          | (have r₁ := b6e15 (σ (k x y)) (σ y)
             have r₂ := b6e158
             grind)
          | exact resolve b6e15 b6e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e1985 : (M.op (σ y) (σ y)) = (k (σ (k x y)) (σ y)) := by grind
        clear b6e1976
        have b6e1990 : (M.op (σ y) (σ y)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b6e1985
             have i₂ := b6e18 (k x y) y
             grind)
          | exact superpose b6e18 b6e1985
          | exact resolve b6e1985 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1985
        have b6e1992 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e1971
             have r₂ := b6e21
             grind)
          | exact resolve b6e1971 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1971
        have b6e1998 : (σ (k x y)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b6e1990
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e1990
          | exact resolve b6e1990 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1990
        have b6e2000 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
          first
          | (have r₁ := b6e1992
             have r₂ := b6e20
             grind)
          | exact resolve b6e1992 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1992
        have b6e2036 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e1998
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e1998
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e1998 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2043 : (τ (σ (k x y))) = (k (k x y) y) := by
          first
          | (have i₁ := b6e13 (k (k x y) y)
             have i₂ := b6e1998
             grind)
          | exact superpose b6e1998 b6e13
          | exact resolve b6e13 b6e1998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1998
        have b6e2075 : (k x y) = (k (k x y) y) := by
          first
          | (have i₁ := b6e2043
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e2043
          | exact resolve b6e2043 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2043
        have b6e2076 : (σ (M.op x y)) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e2036
             have r₂ := b6e21
             grind)
          | exact resolve b6e2036 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2036
        have b6e2085 : (σ (M.op x y)) = (σ (k (M.op x y) y)) := by
          first
          | (have r₁ := b6e2076
             have r₂ := b6e20
             grind)
          | exact resolve b6e2076 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2076
        have b6e2117 : (k x y) = (M.op (k x y) y) ∨ y = (k x y) ∨ (k x y) = (M.op (k x y) y) := by
          first
          | (have i₁ := b6e107 y (k x y)
             have i₂ := b6e2075
             grind)
          | exact superpose b6e2075 b6e107
          | (have j0 := b6e107 y x
             grind)
          | exact resolve b6e107 b6e2075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e107
        have b6e2120 : (k x y) = (M.op (k x y) y) ∨ y = (k x y) := by grind
        clear b6e2117
        have b6e2869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ (M.op x y)) (σ y)
             have i₂ := b6e2000
             grind)
          | exact superpose b6e2000 b6e15
          | (have j0 := b6e15 (σ (M.op x y)) (σ y)
             grind)
          | (have r₁ := b6e15 (σ (M.op x y)) (σ y)
             have r₂ := b6e2000
             grind)
          | exact resolve b6e15 b6e2000
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2000
        have b6e2878 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) := by grind
        clear b6e2869
        have b6e2883 : (M.op (σ y) (σ y)) = (σ (k (M.op x y) y)) := by
          first
          | (have i₁ := b6e2878
             have i₂ := b6e18 (M.op x y) y
             grind)
          | exact superpose b6e18 b6e2878
          | exact resolve b6e2878 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2878
        have b6e2887 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e2883
             have i₂ := b6e2085
             grind)
          | exact superpose b6e2085 b6e2883
          | exact resolve b6e2883 b6e2085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2085 b6e2883
        have b6e2943 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e44
             have i₂ := b6e2887
             grind)
          | exact superpose b6e2887 b6e44
          | exact resolve b6e44 b6e2887
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e2887
        have b6e3178 : (k x y) = (τ (σ (M.op x y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e2943
             grind)
          | exact superpose b6e2943 b6e13
          | exact resolve b6e13 b6e2943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2943
        have b6e3210 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e3178
             have i₂ := b6e13 (M.op x y)
             grind)
          | exact superpose b6e13 b6e3178
          | exact resolve b6e3178 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3178
        have b6e13266 : (k x y) ≠ (k x y) ∨ (M.op y y) = (k (k x y) y) ∨ y = (k x y) := by
          first
          | (have i₁ := b6e15 (k x y) y
             have i₂ := b6e2120
             grind)
          | exact superpose b6e2120 b6e15
          | (have j0 := b6e15 (k x y) y
             grind)
          | (have r₁ := b6e15 (k x y) y
             have r₂ := b6e2120
             grind)
          | exact resolve b6e15 b6e2120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2120
        have b6e13280 : (M.op y y) = (k (k x y) y) ∨ y = (k x y) := by grind
        clear b6e13266
        have b6e13287 : (M.op y y) = (k x y) ∨ y = (k x y) := by
          first
          | (have i₁ := b6e13280
             have i₂ := b6e2075
             grind)
          | exact superpose b6e2075 b6e13280
          | exact resolve b6e13280 b6e2075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2075 b6e13280
        have b6e13292 : (M.op x y) = (M.op y y) ∨ y = (k x y) := by
          first
          | (have i₁ := b6e13287
             have i₂ := b6e3210
             grind)
          | exact superpose b6e3210 b6e13287
          | exact resolve b6e13287 b6e3210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13287
        have b6e13296 : y = (k x y) := by
          first
          | (have r₁ := b6e13292
             have r₂ := b6e21
             grind)
          | exact resolve b6e13292 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13292
        have b6e14052 : y = (M.op x y) := by
          first
          | (have i₁ := b6e3210
             have i₂ := b6e13296
             grind)
          | exact superpose b6e13296 b6e3210
          | exact resolve b6e3210 b6e13296
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3210 b6e13296
        have b6e15224 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e29 x y x
             have i₂ := b6e14052
             grind)
          | exact superpose b6e14052 b6e29
          | exact resolve b6e29 b6e14052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e17066 : y ≠ (M.op x y) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e15224 y
             grind)
          | exact superpose b6e15224 b6e21
          | exact resolve b6e21 b6e15224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15224
        have b6e17151 : False := by grind
        exact b6e17151
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X1 X0) X1) X3
               have i₂ := b7e13 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
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
          have b7e68 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e73 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e68
          have b7e76 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e25
               grind)
            | exact resolve b7e73 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e73
          have b7e81 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e76
            | exact resolve b7e76 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e88 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e81
               grind)
            | exact superpose b7e81 b7e14
            | exact resolve b7e14 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e89 : y = (k x y) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e88
            | exact resolve b7e88 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e127 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e128 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e127
               have r₂ := b7e22
               grind)
            | exact resolve b7e127 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127
          have b7e130 : y = (M.op x y) := by
            first
            | (have r₁ := b7e128
               have r₂ := b7e21
               grind)
            | exact resolve b7e128 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e141 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e130
               grind)
            | exact superpose b7e130 b7e22
            | exact resolve b7e22 b7e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e145 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e31 x y x
               have i₂ := b7e130
               grind)
            | exact superpose b7e130 b7e31
            | exact resolve b7e31 b7e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e130
          have b7e148 : False := by grind
          exact b7e148
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e478 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e86 x y
               grind)
            | exact superpose b8e86 b8e24
            | (have j1 := b8e86 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e86 x y
               grind)
            | exact resolve b8e24 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e525 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e478
          have b8e540 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e525
               have r₂ := b8e23
               grind)
            | exact resolve b8e525 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e525
          have b8e550 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e540
               grind)
            | exact superpose b8e540 b8e20
            | exact resolve b8e20 b8e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e540
          have b8e853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e550
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e550
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e550 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e550
          have b8e854 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e853
          have b8e859 : x = (M.op x y) := by
            first
            | (have r₁ := b8e854
               have r₂ := b8e22
               grind)
            | exact resolve b8e854 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e854
          have b8e864 : False := by grind
          exact b8e864
