import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation3499 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op (M.op X1 X1) X0) X2 x
           have i₂ := b0e11 X0 (M.op x x) X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e36 X0 x X2
           have i₂ := b0e11 X0 (M.op (M.op x x) X0) x
           grind)
        | (have i₁ := b0e36 X0 x X2
           have i₂ := b0e11 (M.op (M.op x x) X0) x X2
           grind)
        | exact superpose b0e11 b0e36
        | exact resolve b0e36 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e46 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e31 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e31
        | exact resolve b0e31 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e117 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e40 (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e157 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e117 (σ x)
           grind)
        | exact superpose b0e117 b0e18
        | exact resolve b0e18 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e162 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e157
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e157
        | exact resolve b0e157 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e157
      have b0e163 : False := by grind
      exact b0e163
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
        have b1e110 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b1e116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e110 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110
        have b1e172 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b1e180 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e172 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e172
          | exact resolve b1e172 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e172
        have b1e457 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e180 (σ y)
             have i₂ := b1e116 (σ y)
             grind)
          | exact superpose b1e116 b1e180
          | (have j1 := b1e116 (σ y)
             grind)
          | exact resolve b1e180 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116 b1e180
        have b1e462 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e457
        have b1e466 : False := by grind
        exact b1e466
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
        have b2e105 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b2e110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e105 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105
        have b2e144 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e149 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e144 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e144
          | exact resolve b2e144 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e144
        have b2e312 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e149 (σ y)
             have i₂ := b2e110 (σ y)
             grind)
          | exact superpose b2e110 b2e149
          | (have j1 := b2e110 (σ y)
             grind)
          | exact resolve b2e149 b2e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e110 b2e149
        have b2e315 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e312
        have b2e319 : False := by grind
        exact b2e319
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
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
        have b3e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e96 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X2 X0
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e116 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e96 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96
        have b3e3841 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e116 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e3842 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e3841 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3841
        have b3e3843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e3842 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3842
        have b3e8270 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e34 y
             have i₂ := b3e3843 y
             grind)
          | exact superpose b3e3843 b3e34
          | (have j1 := b3e3843 y
             grind)
          | exact resolve b3e34 b3e3843
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e3843
        have b3e8276 : y = (M.op y y) := by grind
        clear b3e8270
        have b3e8318 : False := by grind
        exact b3e8318
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
          have b4e69 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
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
          have b4e70 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b4e75 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e76 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e69 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e389 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e75 (σ X0)
               grind)
            | exact superpose b4e75 b4e19
            | (have j1 := b4e75 (σ X0)
               grind)
            | exact resolve b4e19 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e75454 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e389 y
               grind)
            | exact superpose b4e389 b4e23
            | (have j1 := b4e389 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e389 y
               grind)
            | exact resolve b4e23 b4e389
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e389
          have b4e75568 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e75454
          have b4e75632 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e75568
               grind)
            | exact superpose b4e75568 b4e20
            | exact resolve b4e20 b4e75568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75568
          have b4e76634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e75632
               have i₂ := b4e76 y
               grind)
            | exact superpose b4e76 b4e75632
            | (have j1 := b4e76 y
               grind)
            | exact resolve b4e75632 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e75632
          have b4e76649 : y = (M.op y y) := by grind
          clear b4e76634
          have b4e76654 : False := by grind
          exact b4e76654
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
          have b5e81 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          have b5e87 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e314 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e87 (σ x)
               grind)
            | exact superpose b5e87 b5e34
            | (have j1 := b5e87 (σ x)
               grind)
            | exact resolve b5e34 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e87
          have b5e317 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e314
          have b5e321 : False := by grind
          exact b5e321
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e97 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e104 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e97 X0
             grind)
          | (have r₁ := b6e97 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e97 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e97 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e4146 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e104 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e4147 : y = (M.op y y) := by grind
        clear b6e4146
        have b6e4157 : False := by grind
        exact b6e4157
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b7e92 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 X0
               have i₂ := b7e18 X0 x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 x x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e101 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e92 X0
               grind)
            | (have r₁ := b7e92 x
               have r₂ := b7e22
               grind)
            | (have r₁ := b7e92 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e92 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e4429 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have j0 := b7e101 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e4430 : x = (M.op x x) := by grind
          clear b7e4429
          have b7e4441 : False := by grind
          exact b7e4441
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
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
          have b8e32 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op (M.op X1 X1) X0) X2 x
               have i₂ := b8e13 X0 (M.op x x) X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X2
            first
            | (have i₁ := b8e32 X0 x X2
               have i₂ := b8e13 X0 (M.op (M.op x x) X0) x
               grind)
            | (have i₁ := b8e32 X0 x X2
               have i₂ := b8e13 (M.op (M.op x x) X0) x X2
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e76 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e36 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e36
            | (have j1 := b8e18 X2 X2
               grind)
            | exact resolve b8e36 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
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
          have b8e85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e80 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e196 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e85 (σ X0)
               grind)
            | exact superpose b8e85 b8e19
            | (have j1 := b8e85 (σ X0)
               grind)
            | exact resolve b8e19 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e15799 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e196 x
               grind)
            | exact superpose b8e196 b8e20
            | (have j1 := b8e196 x
               grind)
            | exact resolve b8e20 b8e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196
          have b8e16004 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e15799
               have r₂ := b8e24
               grind)
            | exact resolve b8e15799 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15799
          have b8e17620 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op X0 y) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e16004
               have i₂ := b8e76 y X0 x
               grind)
            | exact superpose b8e76 b8e16004
            | (have j1 := b8e76 y X0 x
               grind)
            | exact resolve b8e16004 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e16004
          have b8e17627 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have j0 := b8e17620 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17620
          have b8e17634 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e17627 X0
               grind)
            | (have r₁ := b8e17627 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e17627 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17627
          have b8e18180 : y ≠ y := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e17634 y
               grind)
            | exact superpose b8e17634 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e17634 y
               grind)
            | exact resolve b8e21 b8e17634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17634
          have b8e18181 : False := by grind
          exact b8e18181

/-- `Equation3503`: `x ◇ x = y ◇ ((z ◇ w) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
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
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b1e26 : y ≠ y ∨ x = (k x y) := by
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
        have b1e28 : x = (k x y) := by grind
        clear b1e26
        have b1e67 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e72 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e67
        have b1e73 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e72
             have r₂ := b1e23
             grind)
          | exact resolve b1e72 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e74 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e73
          | exact resolve b1e73 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e75 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e74
          | exact resolve b1e74 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e74
        have b1e76 : False := by grind
        exact b1e76
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b2e24 : y ≠ y ∨ x = (k x y) := by
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
        have b2e25 : x = (k x y) := by grind
        clear b2e24
        have b2e89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e673 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e89 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e12778 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e673 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e673
          | (have j0 := b2e673 x y
             grind)
          | exact resolve b2e673 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e673
        have b2e12787 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e12778
        have b2e12815 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e12787
             have r₂ := b2e22
             grind)
          | exact resolve b2e12787 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12787
        have b2e12832 : False := by grind
        exact b2e12832
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b3e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ x) = (σ (k x y)) := by
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
        have b3e50 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e53 : x = y ∨ y = (k x y) := by grind
        clear b3e50
        have b3e54 : y = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e23
             grind)
          | exact resolve b3e53 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e53
        have b3e57 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e29
          | exact resolve b3e29 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e54
        have b3e58 : False := by grind
        exact b3e58
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
          have b5e66 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e71 : x = y ∨ y = (k x y) := by grind
          clear b5e66
          have b5e72 : y = (k x y) := by
            first
            | (have r₁ := b5e71
               have r₂ := b5e25
               grind)
            | exact resolve b5e71 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e71
          have b5e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e798 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e11070 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e798 x y
               have i₂ := b5e72
               grind)
            | exact superpose b5e72 b5e798
            | (have j0 := b5e798 x y
               grind)
            | exact resolve b5e798 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72 b5e798
          have b5e11079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e11070
          have b5e11082 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e11079
               have r₂ := b5e24
               grind)
            | exact resolve b5e11079 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11079
          have b5e11098 : False := by grind
          exact b5e11098
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e24
        have b6e26 : (σ x) = (σ (k x y)) := by
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
        have b6e31 : (k x y) = (τ (σ x)) := by
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
        have b6e32 : x = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e63 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e65 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e63
        have b6e68 : y = (M.op x y) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e21
             grind)
          | exact resolve b6e65 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e71 : False := by grind
        exact b6e71
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
          have b7e53 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e56 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e53
          have b7e57 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e25
               grind)
            | exact resolve b7e56 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e56
          have b7e58 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e57
            | exact resolve b7e57 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e14
            | exact resolve b7e14 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e62 : y = (k x y) := by
            first
            | (have i₁ := b7e61
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e61
            | exact resolve b7e61 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e71 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e62
               grind)
            | exact superpose b7e62 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e72 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e71
          have b7e74 : x = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e76 : False := by grind
          exact b7e76
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e508 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e547 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e508
               have r₂ := b8e24
               grind)
            | exact resolve b8e508 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e508
          have b8e551 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e547
               have r₂ := b8e23
               grind)
            | exact resolve b8e547 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e547
          have b8e553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e551
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e551
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e551 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e551
          have b8e554 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e553
          have b8e555 : y = (M.op x y) := by
            first
            | (have r₁ := b8e554
               have r₂ := b8e22
               grind)
            | exact resolve b8e554 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e554
          have b8e556 : False := by grind
          exact b8e556

/-- `Equation3503`: `x ◇ x = y ◇ ((z ◇ w) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation3503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3503.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (M.op X3 (M.op X0 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X1 X2) X0) X3 x x
           have i₂ := b0e11 X0 (M.op x x) X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X3 (M.op X0 X0)) := by
        intro X0 X3
        first
        | (have i₁ := b0e36 X0 x x X3
           have i₂ := b0e11 X0 (M.op (M.op x x) X0) x x
           grind)
        | (have i₁ := b0e36 X0 x x X3
           have i₂ := b0e11 (M.op (M.op x x) X0) x x X3
           grind)
        | exact superpose b0e11 b0e36
        | exact resolve b0e36 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e46 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e31 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e31
        | exact resolve b0e31 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e115 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e40 (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e155 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e115 (σ x)
           grind)
        | exact superpose b0e115 b0e18
        | exact resolve b0e18 b0e115
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115
      have b0e160 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e155
           have i₂ := b0e46 x
           grind)
        | exact superpose b0e46 b0e155
        | exact resolve b0e155 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e155
      have b0e161 : False := by grind
      exact b0e161
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
        have b1e108 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b1e114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e108 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e170 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b1e178 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e170 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e170
          | exact resolve b1e170 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e170
        have b1e461 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e178 (σ y)
             have i₂ := b1e114 (σ y)
             grind)
          | exact superpose b1e114 b1e178
          | (have j1 := b1e114 (σ y)
             grind)
          | exact resolve b1e178 b1e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114 b1e178
        have b1e466 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e461
        have b1e470 : False := by grind
        exact b1e470
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
        have b2e103 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
        have b2e108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e103 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103
        have b2e142 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
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
        have b2e147 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e142 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e142
          | exact resolve b2e142 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142
        have b2e317 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e147 (σ y)
             have i₂ := b2e108 (σ y)
             grind)
          | exact superpose b2e108 b2e147
          | (have j1 := b2e108 (σ y)
             grind)
          | exact resolve b2e147 b2e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108 b2e147
        have b2e320 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e317
        have b2e324 : False := by grind
        exact b2e324
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
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
        have b3e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e92 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X2 X0
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e115 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e92 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e3234 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e115 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115
        have b3e3235 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e3234 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3234
        have b3e3236 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e3235 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3235
        have b3e8273 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e34 y
             have i₂ := b3e3236 y
             grind)
          | exact superpose b3e3236 b3e34
          | (have j1 := b3e3236 y
             grind)
          | exact resolve b3e34 b3e3236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e3236
        have b3e8279 : y = (M.op y y) := by grind
        clear b3e8273
        have b3e8323 : False := by grind
        exact b3e8323
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
          have b4e67 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
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
          have b4e68 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b4e73 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e68 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e74 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have j0 := b4e67 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e390 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e73 (σ X0)
               grind)
            | exact superpose b4e73 b4e19
            | (have j1 := b4e73 (σ X0)
               grind)
            | exact resolve b4e19 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e54555 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e390 y
               grind)
            | exact superpose b4e390 b4e23
            | (have j1 := b4e390 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e390 y
               grind)
            | exact resolve b4e23 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e390
          have b4e54658 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e54555
          have b4e54717 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e54658
               grind)
            | exact superpose b4e54658 b4e20
            | exact resolve b4e20 b4e54658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54658
          have b4e55594 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e54717
               have i₂ := b4e74 y
               grind)
            | exact superpose b4e74 b4e54717
            | (have j1 := b4e74 y
               grind)
            | exact resolve b4e54717 b4e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74 b4e54717
          have b4e55609 : y = (M.op y y) := by grind
          clear b4e55594
          have b4e55614 : False := by grind
          exact b4e55614
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
          have b5e81 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
          have b5e87 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e318 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e87 (σ x)
               grind)
            | exact superpose b5e87 b5e34
            | (have j1 := b5e87 (σ x)
               grind)
            | exact resolve b5e34 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e87
          have b5e321 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e318
          have b5e325 : False := by grind
          exact b5e325
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e97 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e104 : ∀ X0 : G, (M.op y X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e97 X0
             grind)
          | (have r₁ := b6e97 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e97 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e97 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e3898 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e104 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e3899 : y = (M.op y y) := by grind
        clear b6e3898
        have b6e3908 : False := by grind
        exact b6e3908
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b7e92 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 X0
               have i₂ := b7e18 X0 x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 x x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e101 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e92 X0
               grind)
            | (have r₁ := b7e92 x
               have r₂ := b7e22
               grind)
            | (have r₁ := b7e92 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e92 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e4168 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have j0 := b7e101 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e4169 : x = (M.op x x) := by grind
          clear b7e4168
          have b7e4179 : False := by grind
          exact b7e4179
        · have b8e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
            intro X0 X1 X2 X3
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
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X1 X2) X0) X3 x x
               have i₂ := b8e13 X0 (M.op x x) X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X3 (M.op X0 X0)) := by
            intro X0 X3
            first
            | (have i₁ := b8e32 X0 x x X3
               have i₂ := b8e13 X0 (M.op (M.op x x) X0) x x
               grind)
            | (have i₁ := b8e32 X0 x x X3
               have i₂ := b8e13 (M.op (M.op x x) X0) x x X3
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e75 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e36 X0 x
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e36
            | (have j1 := b8e18 X2 X2
               grind)
            | exact resolve b8e36 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
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
          have b8e85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e80 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e200 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e85 (σ X0)
               grind)
            | exact superpose b8e85 b8e19
            | (have j1 := b8e85 (σ X0)
               grind)
            | exact resolve b8e19 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e15085 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e200 x
               grind)
            | exact superpose b8e200 b8e20
            | (have j1 := b8e200 x
               grind)
            | exact resolve b8e20 b8e200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200
          have b8e15293 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e15085
               have r₂ := b8e24
               grind)
            | exact resolve b8e15085 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15085
          have b8e16843 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op X0 y) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e15293
               have i₂ := b8e75 y X0 x
               grind)
            | exact superpose b8e75 b8e15293
            | (have j1 := b8e75 y X0 x
               grind)
            | exact resolve b8e15293 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e15293
          have b8e16850 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have j0 := b8e16843 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16843
          have b8e16857 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e16850 X0
               grind)
            | (have r₁ := b8e16850 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e16850 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16850
          have b8e17385 : y ≠ y := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e16857 y
               grind)
            | exact superpose b8e16857 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e16857 y
               grind)
            | exact resolve b8e21 b8e16857
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16857
          have b8e17386 : False := by grind
          exact b8e17386

/-- `Equation3534`: `x ◇ y = x ◇ ((z ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pyx_Equation3534 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3534 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3534.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
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
      have b0e79 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e83 : False := by grind
      exact b0e83
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
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
          have b4e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) y)) := by
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
          have b4e47 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) := by
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
          have b4e112 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
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
          have b4e116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e112
               have i₂ := b4e43 x
               grind)
            | exact superpose b4e43 b4e112
            | exact resolve b4e112 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e112
          have b4e118 : False := by grind
          exact b4e118
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
          have b5e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y y) y)) := by
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
          have b5e58 : (M.op y y) ≠ (M.op y y) ∨ x = y ∨ x = (k x y) := by
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
          have b5e64 : x = y ∨ x = (k x y) := by grind
          clear b5e58
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
          have b5e73 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e76 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
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
          have b5e81 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X0 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e13 X0 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e85 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e81 X0 X1 X2
               have i₂ := b5e13 X2 X1 X0
               grind)
            | exact superpose b5e13 b5e81
            | (have j0 := b5e81 X0 X1 X2
               grind)
            | exact resolve b5e81 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0 X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e73
            | (have j0 := b5e73 X0 X1
               grind)
            | exact resolve b5e73 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e204 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e20
               have i₂ := b5e85 X0 (σ y) (σ x)
               grind)
            | (have i₁ := b5e20
               have i₂ := b5e85 (σ y) x (σ x)
               grind)
            | exact superpose b5e85 b5e20
            | (have j1 := b5e85 X0 (σ y) x
               grind)
            | (have r₁ := b5e20
               have r₂ := b5e85 (σ (M.op x y)) (M.op (σ x) (σ y)) x
               grind)
            | (have r₁ := b5e20
               have r₂ := b5e85 (M.op (σ x) (σ y)) (σ (M.op x y)) x
               grind)
            | exact resolve b5e20 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e221 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e20
               have i₂ := b5e85 (σ y) X0 (σ x)
               grind)
            | (have i₁ := b5e20
               have i₂ := b5e85 X0 (σ y) (σ x)
               grind)
            | exact superpose b5e85 b5e20
            | (have j1 := b5e85 (σ y) X0 x
               grind)
            | (have r₁ := b5e20
               have r₂ := b5e85 (σ (M.op x y)) (M.op (σ x) (σ y)) x
               grind)
            | (have r₁ := b5e20
               have r₂ := b5e85 (M.op (σ x) (σ y)) (σ (M.op x y)) x
               grind)
            | exact resolve b5e20 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e455 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e89 x y
               grind)
            | exact superpose b5e89 b5e20
            | (have j1 := b5e89 x y
               grind)
            | exact resolve b5e20 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e504 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e455
               have r₂ := b5e23
               grind)
            | exact resolve b5e455 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e455
          have b5e526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e504
               have i₂ := b5e43 x
               grind)
            | exact superpose b5e43 b5e504
            | exact resolve b5e504 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e504
          have b5e538 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b5e526
               have r₂ := b5e20
               grind)
            | exact resolve b5e526 b5e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e526
          have b5e550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e538
               have i₂ := b5e84 x y
               grind)
            | exact superpose b5e84 b5e538
            | (have j1 := b5e84 x y
               grind)
            | (have r₁ := b5e538
               have r₂ := b5e84 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b5e538
               have r₂ := b5e84 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b5e538 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e538
          have b5e553 : y = (k y x) ∨ x = y := by grind
          clear b5e550
          have b5e555 : y = (k y x) := by
            first
            | (have r₁ := b5e553
               have r₂ := b5e21
               grind)
            | exact resolve b5e553 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e553
          have b5e6380 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e204 (σ x)
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e204
            | (have j0 := b5e204 (σ x)
               grind)
            | exact resolve b5e204 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e204
          have b5e6413 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e6380
               have r₂ := b5e23
               grind)
            | exact resolve b5e6380 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6380
          have b5e6417 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e6413
               have i₂ := b5e43 x
               grind)
            | exact superpose b5e43 b5e6413
            | exact resolve b5e6413 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6413
          have b5e6418 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b5e6417
          have b5e6419 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e6418
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e6418
            | exact resolve b5e6418 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6418
          have b5e6420 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e6419
               have i₂ := b5e555
               grind)
            | exact superpose b5e555 b5e6419
            | exact resolve b5e6419 b5e555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e555 b5e6419
          have b5e6434 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ y) (σ x)
               have i₂ := b5e6420
               grind)
            | exact superpose b5e6420 b5e13
            | exact resolve b5e13 b5e6420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6420
          have b5e6922 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e221 (σ x)
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e221
            | (have j0 := b5e221 (σ x)
               grind)
            | exact resolve b5e221 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e221
          have b5e6971 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e6922
               have r₂ := b5e23
               grind)
            | exact resolve b5e6922 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6922
          have b5e6975 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b5e6971
               have i₂ := b5e43 x
               grind)
            | exact superpose b5e43 b5e6971
            | exact resolve b5e6971 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e6971
          have b5e6976 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b5e6975
          have b5e6978 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e6976
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e6976
            | exact resolve b5e6976 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6976
          have b5e6979 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e6978
               have i₂ := b5e65
               grind)
            | exact superpose b5e65 b5e6978
            | exact resolve b5e6978 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e6978
          have b5e6988 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e6434 X0
               have i₂ := b5e6979
               grind)
            | exact superpose b5e6979 b5e6434
            | exact resolve b5e6434 b5e6979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6434 b5e6979
          have b5e8137 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e6988 (σ y)
               grind)
            | exact superpose b5e6988 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e6988 (σ y)
               grind)
            | exact resolve b5e24 b5e6988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6988
          have b5e8149 : False := by grind
          exact b5e8149
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
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
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b7e53 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e54 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e53 X0
               have i₂ := b7e13 X0 (σ y) (σ y)
               grind)
            | exact superpose b7e13 b7e53
            | exact resolve b7e53 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
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
          have b7e64 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e60
          have b7e65 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e23
               grind)
            | exact resolve b7e64 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e14
            | exact resolve b7e14 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : x = (k x y) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e69
            | exact resolve b7e69 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e102 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e103 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e102
               have r₂ := b7e22
               grind)
            | exact resolve b7e102 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e105 : x = (M.op y x) := by
            first
            | (have r₁ := b7e103
               have r₂ := b7e21
               grind)
            | exact resolve b7e103 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e113 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e54 (σ x)
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e54
            | exact resolve b7e54 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e115 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e17 X1 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e17
            | (have j0 := b7e17 (σ X0) X1
               grind)
            | exact resolve b7e17 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e120 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e105
               grind)
            | exact superpose b7e105 b7e13
            | exact resolve b7e13 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e679 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e113
               grind)
            | exact superpose b7e113 b7e20
            | exact resolve b7e20 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2737 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e115 x (σ y)
               have i₂ := b7e113
               grind)
            | exact superpose b7e113 b7e115
            | (have j0 := b7e115 x (σ y)
               grind)
            | (have r₁ := b7e115 x (σ y)
               have r₂ := b7e113
               grind)
            | exact resolve b7e115 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113 b7e115
          have b7e2758 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e2737
          have b7e2764 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e2758
               have r₂ := b7e23
               grind)
            | exact resolve b7e2758 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2758
          have b7e2777 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e2764
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e2764
            | exact resolve b7e2764 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2764
          have b7e2792 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e2777
               grind)
            | exact superpose b7e2777 b7e14
            | exact resolve b7e14 b7e2777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2777
          have b7e2834 : y = (k y x) := by
            first
            | (have i₁ := b7e2792
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2792
            | exact resolve b7e2792 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2792
          have b7e3142 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b7e18 y x
               have i₂ := b7e2834
               grind)
            | exact superpose b7e2834 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e2834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2834
          have b7e3143 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e3142
               have r₂ := b7e21
               grind)
            | exact resolve b7e3142 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3142
          have b7e3836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e679
               have i₂ := b7e3143
               grind)
            | exact superpose b7e3143 b7e679
            | exact resolve b7e679 b7e3143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e679 b7e3143
          have b7e3853 : y = (M.op x y) := by grind
          clear b7e3836
          have b7e4030 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e120 X0
               have i₂ := b7e3853
               grind)
            | exact superpose b7e3853 b7e120
            | exact resolve b7e120 b7e3853
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120 b7e3853
          have b7e4181 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e4030 y
               grind)
            | exact superpose b7e4030 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e4030 y
               grind)
            | exact resolve b7e22 b7e4030
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4030
          have b7e4182 : False := by grind
          exact b7e4182
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
          have b8e59 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e17
            | (have j0 := b8e17 (σ X0) X1
               grind)
            | exact resolve b8e17 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e85 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 X0 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e13 X0 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e90 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e91 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e85 X0 X1 X2
               have i₂ := b8e13 X2 X1 X0
               grind)
            | exact superpose b8e13 b8e85
            | (have j0 := b8e85 X0 X1 X2
               grind)
            | exact resolve b8e85 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e235 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e91 (σ x) X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e91 X0 (σ x) (σ y)
               grind)
            | exact superpose b8e91 b8e24
            | (have j1 := b8e91 (σ x) X0 x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e91 (σ y) (σ x) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e91 (σ x) (σ y) (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e91 (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) x
               grind)
            | exact resolve b8e24 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e244 : ∀ X0 : G, (M.op (σ y) X0) ≠ (σ (M.op y y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e235 X0
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e235
            | (have j0 := b8e235 X0
               grind)
            | exact resolve b8e235 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e235
          have b8e476 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e94 x y
               grind)
            | exact superpose b8e94 b8e20
            | (have j1 := b8e94 x y
               grind)
            | exact resolve b8e20 b8e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e534 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e476
               have r₂ := b8e23
               grind)
            | exact resolve b8e476 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e476
          have b8e1992 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e534
               have i₂ := b8e90 x y
               grind)
            | exact superpose b8e90 b8e534
            | (have j1 := b8e90 x y
               grind)
            | (have r₁ := b8e534
               have r₂ := b8e90 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e534
               have r₂ := b8e90 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e534 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e534
          have b8e1995 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k y x) ∨ x = y := by grind
          clear b8e1992
          have b8e2000 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b8e1995
               have r₂ := b8e21
               grind)
            | exact resolve b8e1995 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1995
          have b8e2010 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e59 x (σ y)
               have i₂ := b8e2000
               grind)
            | exact superpose b8e2000 b8e59
            | (have j0 := b8e59 x (σ y)
               grind)
            | (have r₁ := b8e59 x (σ y)
               have r₂ := b8e2000
               grind)
            | exact resolve b8e59 b8e2000
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59 b8e2000
          have b8e2026 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
          clear b8e2010
          have b8e2030 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b8e2026
               have r₂ := b8e23
               grind)
            | exact resolve b8e2026 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2026
          have b8e2033 : (σ y) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e2030
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e2030
            | exact resolve b8e2030 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2030
          have b8e2052 : (k y x) = (τ (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e2033
               grind)
            | exact superpose b8e2033 b8e14
            | exact resolve b8e14 b8e2033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2033
          have b8e2094 : y = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e2052
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e2052
            | exact resolve b8e2052 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2052
          have b8e2095 : y = (k y x) := by grind
          clear b8e2094
          have b8e2178 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e91 x y X0
               have i₂ := b8e2095
               grind)
            | exact superpose b8e2095 b8e91
            | (have j0 := b8e91 y x X0
               grind)
            | exact resolve b8e91 b8e2095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e2181 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e2178 X0
               grind)
            | (have r₁ := b8e2178 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e2178 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2178
          have b8e5186 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e244 (σ y)
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e244
            | (have j0 := b8e244 (σ y)
               grind)
            | (have r₁ := b8e244 (σ y)
               have r₂ := b8e30 y
               grind)
            | exact resolve b8e244 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e244
          have b8e5207 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b8e5186
          have b8e5218 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e5207
               have r₂ := b8e23
               grind)
            | exact resolve b8e5207 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5207
          have b8e5220 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e5218
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e5218
            | exact resolve b8e5218 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5218
          have b8e5222 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e5220
               have i₂ := b8e2095
               grind)
            | exact superpose b8e2095 b8e5220
            | exact resolve b8e5220 b8e2095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2095 b8e5220
          have b8e5232 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e5222
               grind)
            | exact superpose b8e5222 b8e20
            | exact resolve b8e20 b8e5222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5222
          have b8e5310 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e5232
               have i₂ := b8e2181 X0
               grind)
            | exact superpose b8e2181 b8e5232
            | (have j1 := b8e2181 X0
               grind)
            | exact resolve b8e5232 b8e2181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2181 b8e5232
          have b8e5311 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e5310 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5310
          have b8e5852 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e5311 y
               grind)
            | exact superpose b8e5311 b8e22
            | (have r₁ := b8e22
               have r₂ := b8e5311 y
               grind)
            | exact resolve b8e22 b8e5311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5311
          have b8e5853 : False := by grind
          exact b8e5853

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_x_pyx_Equation3583 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : x ≠ x ∨ y = (k x y) := by
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
        have b1e27 : y = (k x y) := by grind
        clear b1e24
        have b1e42 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e42
        have b1e46 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e48 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e46
          | exact resolve b1e46 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e49 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e48
          | exact resolve b1e48 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e48
        have b1e50 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e22
          | exact resolve b1e22 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e21
          | exact resolve b1e21 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e58 : False := by grind
        exact b1e58
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e255 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e60 X1 X0
             grind)
          | exact superpose b2e60 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e60 X1 X0
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X0)
             have r₂ := b2e60 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e60 X0 X1
             grind)
          | exact resolve b2e15 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e256 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e60 x y
             grind)
          | exact superpose b2e60 b2e22
          | (have j1 := b2e60 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e60 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e60 y x
             grind)
          | exact resolve b2e22 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e268 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e256
        have b2e278 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e268
             have r₂ := b2e21
             grind)
          | exact resolve b2e268 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e268
        have b2e279 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e255 X0 X1
             have j1 := b2e15 (σ X1) (σ X0)
             grind)
          | (have r₁ := b2e255 X0 X1
             have r₂ := b2e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e255 X0 X1
             have r₂ := b2e15 (σ X1) (σ X0)
             grind)
          | exact resolve b2e255 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e255
        have b2e289 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e279 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e279
          | (have j0 := b2e279 X0 X1
             grind)
          | exact resolve b2e279 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e279
        have b2e313 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e278
             grind)
          | exact superpose b2e278 b2e21
          | exact resolve b2e21 b2e278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e278
        have b2e644 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e289 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e289
          | (have j0 := b2e289 x y
             grind)
          | exact resolve b2e289 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e289
        have b2e649 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e644
        have b2e652 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e649
             have r₂ := b2e313
             grind)
          | exact resolve b2e649 b2e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e313 b2e649
        have b2e661 : False := by grind
        exact b2e661
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op y x) := by grind
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
        have b3e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op (M.op X0 X0) X1) X3
             have i₂ := b3e12 X0 X1 (M.op X2 X2)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
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
        have b3e37 : (k x y) = (τ (σ y)) := by
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
        have b3e38 : y = (k x y) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e37
          | exact resolve b3e37 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e41 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) := by
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
        have b3e45 : x = (M.op x y) ∨ x = (k x y) := by grind
        clear b3e41
        have b3e47 : x = (k x y) := by
          first
          | (have r₁ := b3e45
             have r₂ := b3e20
             grind)
          | exact resolve b3e45 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e61 : x = y := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e47
          | exact resolve b3e47 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e47
        have b3e65 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e34 y x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e34
          | exact resolve b3e34 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e76 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e65 X0
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e65
          | exact resolve b3e65 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e80 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e23
          | exact resolve b3e23 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e61
        have b3e85 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e76 x
             grind)
          | exact superpose b3e76 b3e80
          | exact resolve b3e80 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76 b3e80
        have b3e86 : False := by grind
        exact b3e86
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X0 X0) X1) X3
               have i₂ := b4e13 X0 X1 (M.op X2 X2)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e37 X0 X1 x X3
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e37
            | exact resolve b4e37 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e40 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e39 y x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e39 (σ y) (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e39
            | exact resolve b4e39 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e200 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e20
            | exact resolve b4e20 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e202 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e200
               have i₂ := b4e40 x
               grind)
            | exact superpose b4e40 b4e200
            | exact resolve b4e200 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e200
          have b4e203 : False := by grind
          exact b4e203
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y x
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : x = (k y x) := by grind
          clear b5e25
          have b5e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e222 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e56 x y
               grind)
            | exact superpose b5e56 b5e24
            | (have j1 := b5e56 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e56 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e56 y x
               grind)
            | exact resolve b5e24 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e234 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e222
          have b5e243 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e234
               have r₂ := b5e23
               grind)
            | exact resolve b5e234 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e234
          have b5e254 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e243
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e243
            | exact resolve b5e243 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e243
          have b5e257 : False := by grind
          exact b5e257
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e56 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
        have b6e58 : y = (M.op y x) ∨ x = (M.op x y) := by grind
        clear b6e56
        have b6e61 : x = (M.op x y) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e21
             grind)
          | exact resolve b6e58 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e64 : False := by grind
        exact b6e64
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ x)
               grind)
            | (have r₁ := b7e16 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e25
          have b7e27 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : x = (k y x) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e67 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e69 : x = (M.op x y) ∨ y = (M.op y x) := by grind
          clear b7e67
          have b7e72 : y = (M.op y x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e76 : False := by grind
          exact b7e76
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e247 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e57 x y
               grind)
            | exact superpose b8e57 b8e24
            | (have j1 := b8e57 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e57 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e57 y x
               grind)
            | exact resolve b8e24 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e259 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e247
          have b8e269 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e259
               have r₂ := b8e23
               grind)
            | exact resolve b8e259 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e259
          have b8e282 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e269
               grind)
            | exact superpose b8e269 b8e20
            | exact resolve b8e20 b8e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e269
          have b8e337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e282
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e282
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e282 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e282
          have b8e338 : x = (M.op x y) ∨ y = (M.op y x) := by grind
          clear b8e337
          have b8e339 : y = (M.op y x) := by
            first
            | (have r₁ := b8e338
               have r₂ := b8e21
               grind)
            | exact resolve b8e338 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e338
          have b8e340 : False := by grind
          exact b8e340

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_y_pyx_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e22 : x = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e38 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b0e12 x x x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e46 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 (M.op y x) X1
             have i₂ := b0e38 (M.op X0 (M.op y x))
             grind)
          | exact superpose b0e38 b0e12
          | exact resolve b0e12 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : ∀ X1 : G, y = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b0e46 x X1
             have i₂ := b0e38 x
             grind)
          | exact superpose b0e38 b0e46
          | exact resolve b0e46 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38 b0e46
        have b0e61 : x = y := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e47 y
             grind)
          | exact superpose b0e47 b0e22
          | exact resolve b0e22 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e92 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e61
             grind)
          | exact superpose b0e61 b0e19
          | exact resolve b0e19 b0e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e61
        have b0e99 : (σ y) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e92
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e92
          | exact resolve b0e92 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e92
        have b0e100 : False := by grind
        exact b0e100
      · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b1e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e20
            | exact resolve b1e20 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b1e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e44 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e42 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e42
            | exact resolve b1e42 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e103 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e44 (σ x) (σ x) x
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e44
            | exact resolve b1e44 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e44
          have b1e164 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e103 (σ x)
               grind)
            | exact superpose b1e103 b1e26
            | (have r₁ := b1e26
               have r₂ := b1e103 (σ x)
               grind)
            | exact resolve b1e26 b1e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26 b1e103
          have b1e165 : False := by grind
          exact b1e165
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e24 : y ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e37 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b2e13 x x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e46 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 (M.op y x) X1
               have i₂ := b2e37 (M.op X0 (M.op y x))
               grind)
            | exact superpose b2e37 b2e13
            | exact resolve b2e13 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e47 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b2e46 x X1
               have i₂ := b2e37 x
               grind)
            | exact superpose b2e37 b2e46
            | exact resolve b2e46 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e37 b2e46
          have b2e59 : y ≠ y := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e47 x
               grind)
            | exact superpose b2e47 b2e24
            | (have r₁ := b2e24
               have r₂ := b2e47 x
               grind)
            | exact resolve b2e24 b2e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e47
          have b2e61 : False := by grind
          exact b2e61
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op x x) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b3e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : x = (k x y) := by grind
          have b3e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b3e13 x x x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 (M.op y x) X1
               have i₂ := b3e32 (M.op X0 (M.op y x))
               grind)
            | exact superpose b3e32 b3e13
            | exact resolve b3e13 b3e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e41 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b3e40 x X1
               have i₂ := b3e32 x
               grind)
            | exact superpose b3e32 b3e40
            | exact resolve b3e40 b3e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e32 b3e40
          have b3e45 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e48 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b3e45
          have b3e49 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e48
               have r₂ := b3e22
               grind)
            | exact resolve b3e48 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e48
          have b3e52 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b3e49
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e49
            | exact resolve b3e49 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e49
          have b3e53 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e52
               have i₂ := b3e26
               grind)
            | exact superpose b3e26 b3e52
            | exact resolve b3e52 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e52
          have b3e54 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e53
               grind)
            | exact superpose b3e53 b3e20
            | exact resolve b3e20 b3e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e55 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e53
               grind)
            | exact superpose b3e53 b3e23
            | exact resolve b3e23 b3e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e62 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e54
               have i₂ := b3e55
               grind)
            | exact superpose b3e55 b3e54
            | exact resolve b3e54 b3e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e54 b3e55
          have b3e63 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e62
               have i₂ := b3e41 x
               grind)
            | exact superpose b3e41 b3e62
            | exact resolve b3e62 b3e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e41 b3e62
          have b3e64 : False := by grind
          exact b3e64
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : y = (M.op x x) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b4e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e21
              | exact resolve b4e21 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e29 : x = (k x y) := by grind
            have b4e47 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e18 (σ x) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b4e47
            have b4e54 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e50
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e50 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e50
            have b4e56 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b4e54
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e54
              | exact resolve b4e54 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e54
            have b4e57 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e56
                 have i₂ := b4e29
                 grind)
              | exact superpose b4e29 b4e56
              | exact resolve b4e56 b4e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29 b4e56
            have b4e77 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e28
                 have i₂ := b4e57
                 grind)
              | exact superpose b4e57 b4e28
              | exact resolve b4e28 b4e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e28
            have b4e78 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b4e24
                 have i₂ := b4e57
                 grind)
              | exact superpose b4e57 b4e24
              | exact resolve b4e24 b4e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e57
            have b4e85 : False := by grind
            exact b4e85
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : x = (k x y) := by grind
            have b5e31 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
              intro X0
              first
              | (have i₁ := b5e14 x x x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e40 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X0 (M.op y x) X1
                 have i₂ := b5e31 (M.op X0 (M.op y x))
                 grind)
              | exact superpose b5e31 b5e14
              | exact resolve b5e14 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e41 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b5e40 x X1
                 have i₂ := b5e31 x
                 grind)
              | exact superpose b5e31 b5e40
              | exact resolve b5e40 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31 b5e40
            have b5e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b5e18 (σ x) (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e18
              | (have j0 := b5e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b5e18 (σ x) (σ y)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e18 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e47 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b5e44
            have b5e50 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e47
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e47 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e47
            have b5e51 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e50
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e50
              | exact resolve b5e50 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e50
            have b5e52 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e51
                 have i₂ := b5e28
                 grind)
              | exact superpose b5e28 b5e51
              | exact resolve b5e51 b5e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e28 b5e51
            have b5e53 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e52
                 grind)
              | exact superpose b5e52 b5e21
              | exact resolve b5e21 b5e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e54 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e24
                 have i₂ := b5e52
                 grind)
              | exact superpose b5e52 b5e24
              | exact resolve b5e24 b5e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e61 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b5e53
                 have i₂ := b5e54
                 grind)
              | exact superpose b5e54 b5e53
              | exact resolve b5e53 b5e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e53 b5e54
            have b5e62 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e61
                 have i₂ := b5e41 x
                 grind)
              | exact superpose b5e41 b5e61
              | exact resolve b5e61 b5e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e41 b5e61
            have b5e63 : False := by grind
            exact b5e63
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e30 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b6e13 x x x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X0 (M.op y x) X1
               have i₂ := b6e30 (M.op X0 (M.op y x))
               grind)
            | exact superpose b6e30 b6e13
            | exact resolve b6e13 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e40 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b6e39 x X1
               have i₂ := b6e30 x
               grind)
            | exact superpose b6e30 b6e39
            | exact resolve b6e39 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e39
          have b6e49 : y = (k y y) := by grind
          have b6e53 : x = y := by
            first
            | (have i₁ := b6e24
               have i₂ := b6e40 y
               grind)
            | exact superpose b6e40 b6e24
            | exact resolve b6e24 b6e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e40
          have b6e58 : x = (k x x) := by
            first
            | (have i₁ := b6e49
               have i₂ := b6e53
               grind)
            | exact superpose b6e53 b6e49
            | exact resolve b6e49 b6e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e49
          have b6e74 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e22
               have i₂ := b6e18 (σ x) X0
               grind)
            | (have i₁ := b6e22
               have i₂ := b6e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b6e18 b6e22
            | (have j1 := b6e18 (σ x) X0
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e22 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e79 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e74 X0
               have i₂ := b6e53
               grind)
            | exact superpose b6e53 b6e74
            | (have j0 := b6e74 X0
               grind)
            | exact resolve b6e74 b6e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e74
          have b6e82 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e53
               grind)
            | exact superpose b6e53 b6e23
            | exact resolve b6e23 b6e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e53
          have b6e315 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have j0 := b6e79 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e79
          have b6e316 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
            first
            | (have r₁ := b6e315
               have r₂ := b6e82
               grind)
            | exact resolve b6e315 b6e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e315
          have b6e317 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
            first
            | (have i₁ := b6e316
               have i₂ := b6e19 x x
               grind)
            | exact superpose b6e19 b6e316
            | exact resolve b6e316 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e316
          have b6e318 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e317
               have i₂ := b6e58
               grind)
            | exact superpose b6e58 b6e317
            | exact resolve b6e317 b6e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e58 b6e317
          have b6e319 : False := by grind
          exact b6e319
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : y = (M.op x x) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b7e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e29 : x = (k x y) := by grind
            have b7e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b7e23
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e23
                 have i₂ := b7e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b7e19 b7e23
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e23 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e265 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e66 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e66
            have b7e266 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e265
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e265 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e265
            have b7e267 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e266
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e266
              | exact resolve b7e266 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e266
            have b7e268 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e267
                 have i₂ := b7e29
                 grind)
              | exact superpose b7e29 b7e267
              | exact resolve b7e267 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e267
            have b7e269 : False := by grind
            exact b7e269
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b8e22 : y = (M.op x x) := by grind
            have b8e26 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
              intro X0
              first
              | (have i₁ := b8e14 x x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X0 (M.op y x) X1
                 have i₂ := b8e31 (M.op X0 (M.op y x))
                 grind)
              | exact superpose b8e31 b8e14
              | exact resolve b8e14 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e40 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b8e39 x X1
                 have i₂ := b8e31 x
                 grind)
              | exact superpose b8e31 b8e39
              | exact resolve b8e39 b8e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31 b8e39
            have b8e51 : y ≠ y := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e40 x
                 grind)
              | exact superpose b8e40 b8e26
              | (have r₁ := b8e26
                 have r₂ := b8e40 x
                 grind)
              | exact resolve b8e26 b8e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40
            have b8e53 : False := by grind
            exact b8e53
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : y ≠ (M.op x x) := by grind
          have b9e22 : x = (M.op y x) := by grind
          have b9e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e27 : (σ x) = (k (σ x) (σ y)) := by grind
          have b9e28 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b9e27
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e27
            | exact resolve b9e27 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e29 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e28
               grind)
            | exact superpose b9e28 b9e14
            | exact resolve b9e14 b9e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e28
          have b9e30 : x = (k x y) := by
            first
            | (have i₁ := b9e29
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e29
            | exact resolve b9e29 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e29
          have b9e43 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b9e13 y x x
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e53 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X1 x) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 (M.op x x) X1
               have i₂ := b9e43 (M.op X0 (M.op x x))
               grind)
            | exact superpose b9e43 b9e13
            | exact resolve b9e13 b9e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e54 : ∀ X1 : G, x = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b9e53 x X1
               have i₂ := b9e43 x
               grind)
            | exact superpose b9e43 b9e53
            | exact resolve b9e53 b9e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e43 b9e53
          have b9e56 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e61 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b9e56
          have b9e64 : y = (k x y) := by
            first
            | (have r₁ := b9e61
               have r₂ := b9e21
               grind)
            | exact resolve b9e61 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e61
          have b9e66 : x = y := by
            first
            | (have i₁ := b9e64
               have i₂ := b9e30
               grind)
            | exact superpose b9e30 b9e64
            | exact resolve b9e64 b9e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30 b9e64
          have b9e68 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e66
               grind)
            | exact superpose b9e66 b9e20
            | exact resolve b9e20 b9e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e74 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e68
               have i₂ := b9e54 x
               grind)
            | exact superpose b9e54 b9e68
            | exact resolve b9e68 b9e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e54 b9e68
          have b9e75 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b9e74
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e74
            | exact resolve b9e74 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e74
          have b9e76 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b9e75
               have i₂ := b9e66
               grind)
            | exact superpose b9e66 b9e75
            | exact resolve b9e75 b9e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e66 b9e75
          have b9e77 : False := by grind
          exact b9e77
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : y ≠ (M.op x x) := by grind
            have b10e23 : x = (M.op y x) := by grind
            have b10e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b10e25 : x ≠ (M.op y y) := by grind
            have b10e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e29 : (σ x) = (k (σ x) (σ y)) := by grind
            have b10e30 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b10e29
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e29
              | exact resolve b10e29 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e29
            have b10e31 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e30
                 grind)
              | exact superpose b10e30 b10e15
              | exact resolve b10e15 b10e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : x = (k x y) := by
              first
              | (have i₁ := b10e31
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e31
              | exact resolve b10e31 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e31
            have b10e62 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
              first
              | (have i₁ := b10e18 x y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e18
              | (have j0 := b10e18 x y
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e23
                 grind)
              | exact resolve b10e18 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e63 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b10e62
            have b10e65 : y = (k x y) := by
              first
              | (have r₁ := b10e63
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e63 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e63
            have b10e69 : x = y := by
              first
              | (have i₁ := b10e65
                 have i₂ := b10e32
                 grind)
              | exact superpose b10e32 b10e65
              | exact resolve b10e65 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32 b10e65
            have b10e75 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e69
                 grind)
              | exact superpose b10e69 b10e25
              | exact resolve b10e25 b10e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e76 : x = (M.op x x) := by
              first
              | (have i₁ := b10e26
                 have i₂ := b10e69
                 grind)
              | exact superpose b10e69 b10e26
              | exact resolve b10e26 b10e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e69
            have b10e82 : False := by grind
            exact b10e82
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x x) := by grind
            have b11e23 : x = (M.op y x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b11e26 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b11e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e28
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e28
              | exact resolve b11e28 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28
            have b11e30 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e29
                 grind)
              | exact superpose b11e29 b11e15
              | exact resolve b11e15 b11e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e31 : x = (k x y) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e30
              | exact resolve b11e30 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e44 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b11e14 y x x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e53 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X0 (M.op x x) X1
                 have i₂ := b11e44 (M.op X0 (M.op x x))
                 grind)
              | exact superpose b11e44 b11e14
              | exact resolve b11e14 b11e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e54 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b11e53 x X1
                 have i₂ := b11e44 x
                 grind)
              | exact superpose b11e44 b11e53
              | exact resolve b11e53 b11e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e44 b11e53
            have b11e56 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
              first
              | (have i₁ := b11e18 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x y
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e60 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b11e56
            have b11e63 : y = (k x y) := by
              first
              | (have r₁ := b11e60
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e60 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e65 : x = y := by
              first
              | (have i₁ := b11e63
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e63
              | exact resolve b11e63 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31 b11e63
            have b11e70 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e65
                 grind)
              | exact superpose b11e65 b11e26
              | exact resolve b11e26 b11e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e65
            have b11e73 : False := by grind
            exact b11e73
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b12e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b12e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b12e25 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b12e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : y = (k y x) := by grind
            have b12e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 (τ X0) X1
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e20
              | exact resolve b12e20 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e32 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b12e14 y y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X2 (M.op (M.op X0 X1) X1) X3
                 have i₂ := b12e14 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e35 X0 X1 x X3
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e35
              | exact resolve b12e35 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e35
            have b12e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X1 X0
                 have i₂ := b12e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b12e19 b12e20
              | (have j1 := b12e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b12e20 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e96 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b12e37 (σ y) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e37
              | exact resolve b12e37 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e107 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 X1 x
                 have i₂ := b12e37 (M.op X0 X1) X1 x
                 grind)
              | exact superpose b12e37 b12e14
              | exact resolve b12e14 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e109 : x = (M.op x y) := by
              first
              | (have i₁ := b12e32 x
                 have i₂ := b12e37 x y x
                 grind)
              | exact superpose b12e37 b12e32
              | exact resolve b12e32 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e32
            have b12e112 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e18 (M.op X0 X1) X2
                 have i₂ := b12e37 X0 X1 X2
                 grind)
              | exact superpose b12e37 b12e18
              | (have j0 := b12e18 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b12e18 (M.op X0 X1) x
                 have r₂ := b12e37 X0 X1 x
                 grind)
              | exact resolve b12e18 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e115 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b12e112 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e112
            have b12e118 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e115 X0 X1 X2
                 have i₂ := b12e37 X0 X1 (M.op X0 X1)
                 grind)
              | exact superpose b12e37 b12e115
              | (have j0 := b12e115 X0 X1 X2
                 grind)
              | exact resolve b12e115 b12e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e115
            have b12e124 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0
              grind
            clear b12e29
            have b12e129 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e124 X0
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e124
              | exact resolve b12e124 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e124
            have b12e144 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b12e24
                 have i₂ := b12e96 (σ x)
                 grind)
              | exact superpose b12e96 b12e24
              | exact resolve b12e24 b12e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e96
            have b12e435 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b12e64 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e64
            have b12e746 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
              intro X0 X1
              first
              | (have i₁ := b12e129 (M.op X0 X1)
                 have i₂ := b12e118 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                 grind)
              | exact superpose b12e118 b12e129
              | (have j1 := b12e118 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                 grind)
              | exact resolve b12e129 b12e118
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e118 b12e129
            have b12e748 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
              intro X0 X1
              first
              | (have j0 := b12e746 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e746
            have b12e2167 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e435 x y
                 have i₂ := b12e28
                 grind)
              | exact superpose b12e28 b12e435
              | (have j0 := b12e435 x y
                 grind)
              | exact resolve b12e435 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e435
            have b12e2177 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
            clear b12e2167
            have b12e17580 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e107 (σ y) (σ y)
                 have i₂ := b12e2177
                 grind)
              | exact superpose b12e2177 b12e107
              | exact resolve b12e107 b12e2177
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e107 b12e2177
            have b12e772605 : (σ y) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e748 (σ x) (σ y)
                 have i₂ := b12e17580
                 grind)
              | exact superpose b12e17580 b12e748
              | exact resolve b12e748 b12e17580
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e748 b12e17580
            have b12e772617 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e772605
                 have i₂ := b12e15 y
                 grind)
              | exact superpose b12e15 b12e772605
              | exact resolve b12e772605 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e772605
            have b12e772621 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e772617
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e772617
              | exact resolve b12e772617 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e772617
            have b12e772623 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b12e772621
                 have r₂ := b12e144
                 grind)
              | exact resolve b12e772621 b12e144
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e144 b12e772621
            have b12e772667 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e772623
                 grind)
              | exact superpose b12e772623 b12e21
              | exact resolve b12e21 b12e772623
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e772623
            have b12e772798 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e772667
                 have i₂ := b12e109
                 grind)
              | exact superpose b12e109 b12e772667
              | exact resolve b12e772667 b12e109
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e109 b12e772667
            have b12e772799 : False := by grind
            exact b12e772799
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e22
                | exact resolve b13e22 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e35 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
                intro X0
                first
                | (have i₁ := b13e15 x y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b13e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b13e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b13e37 X0 X1 x X3
                   have i₂ := b13e15 X0 X1 x
                   grind)
                | exact superpose b13e15 b13e37
                | exact resolve b13e37 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e37
              have b13e43 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 (M.op y y) X1
                   have i₂ := b13e35 (M.op X0 (M.op y y))
                   grind)
                | exact superpose b13e35 b13e15
                | exact resolve b13e15 b13e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e44 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b13e43 x X1
                   have i₂ := b13e35 x
                   grind)
                | exact superpose b13e35 b13e43
                | exact resolve b13e43 b13e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e35 b13e43
              have b13e67 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 X1 X0
                   have i₂ := b13e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b13e20 b13e21
                | (have j1 := b13e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b13e21 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e91 : y = (k y y) := by grind
              clear b13e44
              have b13e419 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b13e67 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e67
              have b13e421 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b13e419 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e419
              have b13e1244 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b13e421 y
                   have i₂ := b13e91
                   grind)
                | exact superpose b13e91 b13e421
                | (have j0 := b13e421 y
                   grind)
                | exact resolve b13e421 b13e91
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e91 b13e421
              have b13e1248 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e1244
              have b13e1267 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b13e39 (σ y) (σ y) x
                   have i₂ := b13e1248
                   grind)
                | exact superpose b13e1248 b13e39
                | exact resolve b13e39 b13e1248
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e39 b13e1248
              have b13e1391 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b13e30
                   have i₂ := b13e1267 (σ x)
                   grind)
                | exact superpose b13e1267 b13e30
                | (have r₁ := b13e30
                   have r₂ := b13e1267 (σ x)
                   grind)
                | exact resolve b13e30 b13e1267
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e1267
              have b13e1408 : False := by grind
              exact b13e1408
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e27 : x ≠ (M.op y y) := by grind
              have b14e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 (τ X0) X1
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e21
                | exact resolve b14e21 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b14e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e35 X0 X1 x X3
                   have i₂ := b14e15 X0 X1 x
                   grind)
                | exact superpose b14e15 b14e35
                | exact resolve b14e35 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e35
              have b14e64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e94 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e19 (M.op X0 X1) X2
                   have i₂ := b14e37 X0 X1 X2
                   grind)
                | exact superpose b14e37 b14e19
                | (have j0 := b14e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b14e19 (M.op X0 X1) x
                   have r₂ := b14e37 X0 X1 x
                   grind)
                | exact resolve b14e19 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e97 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b14e94 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e94
              have b14e100 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e97 X0 X1 X2
                   have i₂ := b14e37 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b14e37 b14e97
                | (have j0 := b14e97 X0 X1 X2
                   grind)
                | exact resolve b14e97 b14e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e97
              have b14e102 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                grind
              clear b14e30
              have b14e107 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e102 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e102
                | exact resolve b14e102 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e102
              have b14e113 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e31 X0 X1
                   have i₂ := b14e20 X1 (τ X0)
                   grind)
                | exact superpose b14e20 b14e31
                | (have j1 := b14e20 X1 (τ X0)
                   grind)
                | exact resolve b14e31 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31
              have b14e191 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e64 (σ X1) (σ X0)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e64
                | (have j0 := b14e64 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e64 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64
              have b14e691 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b14e107 (M.op X0 X1)
                   have i₂ := b14e100 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact superpose b14e100 b14e107
                | (have j1 := b14e100 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b14e107 b14e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e100 b14e107
              have b14e693 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b14e691 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e691
              have b14e1514 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e113 (σ X0) X1
                   have i₂ := b14e16 X0
                   grind)
                | exact superpose b14e16 b14e113
                | exact resolve b14e113 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e113
              have b14e1600 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e1514 X0 X1
                   have i₂ := b14e21 X1 X0
                   grind)
                | exact superpose b14e21 b14e1514
                | (have j0 := b14e1514 X0 X1
                   grind)
                | exact resolve b14e1514 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1514
              have b14e2390 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e191 y x
                   grind)
                | exact superpose b14e191 b14e22
                | (have j1 := b14e191 y x
                   grind)
                | exact resolve b14e22 b14e191
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e191
              have b14e12405 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b14e693 X0 X1
                   grind)
                | exact superpose b14e693 b14e16
                | exact resolve b14e16 b14e693
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e693
              have b14e29998 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b14e12405 X0 X1
                   grind)
                | exact superpose b14e12405 b14e37
                | exact resolve b14e37 b14e12405
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37 b14e12405
              have b14e64505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b14e2390
                   have i₂ := b14e1600 x y
                   grind)
                | exact superpose b14e1600 b14e2390
                | (have j1 := b14e1600 x y
                   grind)
                | (have r₁ := b14e2390
                   have r₂ := b14e1600 x y
                   grind)
                | exact resolve b14e2390 b14e1600
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1600 b14e2390
              have b14e64509 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
              clear b14e64505
              have b14e64523 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b14e64509
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e64509 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64509
              have b14e64534 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b14e64523
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e64523 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64523
              have b14e427010 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e29998 (σ x) (σ y) x
                   have i₂ := b14e64534
                   grind)
                | exact superpose b14e64534 b14e29998
                | exact resolve b14e29998 b14e64534
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29998 b14e64534
              have b14e427019 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
                intro X0
                first
                | (have i₁ := b14e427010 X0
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e427010
                | exact resolve b14e427010 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e427010
              have b14e430015 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e16 (M.op x y)
                   have i₂ := b14e427019 X0
                   grind)
                | exact superpose b14e427019 b14e16
                | (have j1 := b14e427019 X0
                   grind)
                | exact resolve b14e16 b14e427019
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e427019
              have b14e430049 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e430015 X0
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e430015
                | (have j0 := b14e430015 x
                   grind)
                | exact resolve b14e430015 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e430015
              have b14e430051 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have j0 := b14e430049 X0
                   grind)
                | (have r₁ := b14e430049 X0
                   have r₂ := b14e28
                   grind)
                | (have r₁ := b14e430049 x
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e430049 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e430049
              have b14e431858 : y ≠ y := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e430051 x
                   grind)
                | exact superpose b14e430051 b14e28
                | (have r₁ := b14e28
                   have r₂ := b14e430051 x
                   grind)
                | exact resolve b14e28 b14e430051
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e430051
              have b14e431948 : False := by grind
              exact b14e431948
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : x = (M.op y x) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e31 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b15e14 y x x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
              intro X0 X1
              grind
            have b15e40 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 (M.op x x) X1
                 have i₂ := b15e31 (M.op X0 (M.op x x))
                 grind)
              | exact superpose b15e31 b15e14
              | exact resolve b15e14 b15e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e41 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b15e40 x X1
                 have i₂ := b15e31 x
                 grind)
              | exact superpose b15e31 b15e40
              | exact resolve b15e40 b15e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e31 b15e40
            have b15e43 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
              first
              | (have i₁ := b15e18 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x y
                 grind)
              | (have r₁ := b15e18 x y
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e47 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b15e43
            have b15e50 : y = (k x y) := by
              first
              | (have r₁ := b15e47
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e47 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e47
            have b15e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e24
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | (have i₁ := b15e24
                 have i₂ := b15e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b15e19 b15e24
              | (have j1 := b15e19 (σ x) X0
                 grind)
              | (have r₁ := b15e24
                 have r₂ := b15e19 (σ x) (σ y)
                 grind)
              | exact resolve b15e24 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e72 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e41 x
                 grind)
              | exact superpose b15e41 b15e22
              | exact resolve b15e22 b15e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e41
            have b15e255 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b15e67 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e67
            have b15e256 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b15e255
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e255 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e255
            have b15e257 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b15e256
                 have i₂ := b15e20 x y
                 grind)
              | exact superpose b15e20 b15e256
              | exact resolve b15e256 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e256
            have b15e258 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e257
                 have i₂ := b15e50
                 grind)
              | exact superpose b15e50 b15e257
              | exact resolve b15e257 b15e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e50 b15e257
            have b15e259 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e258
                 grind)
              | exact superpose b15e258 b15e25
              | exact resolve b15e25 b15e258
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e261 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) := by
              first
              | (have i₁ := b15e35 (σ y) (σ x)
                 have i₂ := b15e258
                 grind)
              | exact superpose b15e258 b15e35
              | exact resolve b15e35 b15e258
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35
            have b15e267 : (σ y) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b15e261
                 have i₂ := b15e258
                 grind)
              | exact superpose b15e258 b15e261
              | exact resolve b15e261 b15e258
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e258 b15e261
            have b15e268 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b15e267
                 have i₂ := b15e20 y y
                 grind)
              | exact superpose b15e20 b15e267
              | exact resolve b15e267 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e267
            have b15e505 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b15e268
                 have i₂ := b15e19 y y
                 grind)
              | exact superpose b15e19 b15e268
              | (have j1 := b15e19 y y
                 grind)
              | exact resolve b15e268 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e268
            have b15e512 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
            clear b15e505
            have b15e517 : (σ x) = (σ y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b15e512
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e512
              | exact resolve b15e512 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e512
            have b15e522 : y = (M.op y y) := by
              first
              | (have r₁ := b15e517
                 have r₂ := b15e259
                 grind)
              | exact resolve b15e517 b15e259
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e259 b15e517
            have b15e526 : x = y := by
              first
              | (have i₁ := b15e522
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e522
              | exact resolve b15e522 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e522
            have b15e530 : False := by grind
            exact b15e530
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b16e23 : y ≠ (M.op x x) := by grind
              have b16e24 : x = (M.op y x) := by grind
              have b16e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e22
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e22
                | exact resolve b16e22 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b16e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b16e36 X0 X1 x X3
                   have i₂ := b16e15 X0 X1 x
                   grind)
                | exact superpose b16e15 b16e36
                | exact resolve b16e36 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36
              have b16e45 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x y
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e50 : y = (M.op x x) ∨ y = (k x y) := by grind
              clear b16e45
              have b16e54 : y = (k x y) := by
                first
                | (have r₁ := b16e50
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e50 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e50
              have b16e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b16e25
                   have i₂ := b16e20 (σ x) X0
                   grind)
                | (have i₁ := b16e25
                   have i₂ := b16e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b16e20 b16e25
                | (have j1 := b16e20 (σ x) X0
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e25 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e252 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b16e69 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e69
              have b16e253 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b16e252
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e252 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e252
              have b16e254 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e253
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e253
                | exact resolve b16e253 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e253
              have b16e255 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e254
                   have i₂ := b16e54
                   grind)
                | exact superpose b16e54 b16e254
                | exact resolve b16e254 b16e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e54 b16e254
              have b16e258 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b16e38 (σ y) (σ x) x
                   have i₂ := b16e255
                   grind)
                | exact superpose b16e255 b16e38
                | exact resolve b16e38 b16e255
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e38 b16e255
              have b16e392 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b16e30
                   have i₂ := b16e258 (σ x)
                   grind)
                | exact superpose b16e258 b16e30
                | (have r₁ := b16e30
                   have r₂ := b16e258 (σ x)
                   grind)
                | exact resolve b16e30 b16e258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e30 b16e258
              have b16e405 : False := by grind
              exact b16e405
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op x x) := by grind
              have b17e24 : x = (M.op y x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b17e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
                intro X0 X1
                grind
              have b17e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b17e34 X0 X1 x X3
                   have i₂ := b17e15 X0 X1 x
                   grind)
                | exact superpose b17e15 b17e34
                | exact resolve b17e34 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e34
              have b17e43 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
                first
                | (have i₁ := b17e19 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x y
                   grind)
                | (have r₁ := b17e19 x y
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46 : y = (M.op x x) ∨ y = (k x y) := by grind
              clear b17e43
              have b17e49 : y = (k x y) := by
                first
                | (have r₁ := b17e46
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e46 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e222 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e64 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e64
              have b17e223 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e222
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e222 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e222
              have b17e224 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e223
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e223
                | exact resolve b17e223 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e223
              have b17e225 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e224
                   have i₂ := b17e49
                   grind)
                | exact superpose b17e49 b17e224
                | exact resolve b17e224 b17e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e49 b17e224
              have b17e228 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) := by
                first
                | (have i₁ := b17e35 (σ y) (σ x)
                   have i₂ := b17e225
                   grind)
                | exact superpose b17e225 b17e35
                | exact resolve b17e35 b17e225
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e234 : (σ y) = (k (σ y) (σ y)) := by
                first
                | (have i₁ := b17e228
                   have i₂ := b17e225
                   grind)
                | exact superpose b17e225 b17e228
                | exact resolve b17e228 b17e225
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e225 b17e228
              have b17e235 : (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b17e234
                   have i₂ := b17e21 y y
                   grind)
                | exact superpose b17e21 b17e234
                | exact resolve b17e234 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e234
              have b17e443 : (k y y) = (τ (σ y)) := by
                first
                | (have i₁ := b17e16 (k y y)
                   have i₂ := b17e235
                   grind)
                | exact superpose b17e235 b17e16
                | exact resolve b17e16 b17e235
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e235
              have b17e455 : y = (k y y) := by
                first
                | (have i₁ := b17e443
                   have i₂ := b17e16 y
                   grind)
                | exact superpose b17e16 b17e443
                | exact resolve b17e443 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e443
              have b17e500 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e20 y y
                   have i₂ := b17e455
                   grind)
                | exact superpose b17e455 b17e20
                | (have j0 := b17e20 y y
                   grind)
                | exact resolve b17e20 b17e455
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e455
              have b17e501 : y = (M.op y y) := by grind
              clear b17e500
              have b17e543 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b17e36 y y x
                   have i₂ := b17e501
                   grind)
                | exact superpose b17e501 b17e36
                | exact resolve b17e36 b17e501
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36 b17e501
              have b17e585 : y ≠ y := by
                first
                | (have i₁ := b17e28
                   have i₂ := b17e543 x
                   grind)
                | exact superpose b17e543 b17e28
                | (have r₁ := b17e28
                   have r₂ := b17e543 x
                   grind)
                | exact resolve b17e28 b17e543
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e543
              have b17e599 : False := by grind
              exact b17e599
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b18e22 : x ≠ (M.op y x) := by grind
          have b18e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e43 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b18e13 y y x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e52 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 (M.op x y) X1
               have i₂ := b18e43 (M.op X0 (M.op x y))
               grind)
            | exact superpose b18e43 b18e13
            | exact resolve b18e13 b18e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e53 : ∀ X1 : G, x = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b18e52 x X1
               have i₂ := b18e43 x
               grind)
            | exact superpose b18e43 b18e52
            | exact resolve b18e52 b18e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43 b18e52
          have b18e62 : x ≠ x := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e53 y
               grind)
            | exact superpose b18e53 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e53 y
               grind)
            | exact resolve b18e22 b18e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e53
          have b18e68 : False := by grind
          exact b18e68
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op x x) := by grind
            have b19e23 : x ≠ (M.op y x) := by grind
            have b19e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e29 : (σ x) = (k (σ x) (σ y)) := by grind
            have b19e30 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e29
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e29
              | exact resolve b19e29 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29
            have b19e31 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e30
                 grind)
              | exact superpose b19e30 b19e15
              | exact resolve b19e15 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : x = (k x y) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e31
              | exact resolve b19e31 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e76 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b19e32
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e32
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e32 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e85 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b19e76
            have b19e89 : y = (M.op x x) := by
              first
              | (have r₁ := b19e85
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e85 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e85
            have b19e92 : False := by grind
            exact b19e92
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x x) := by grind
            have b20e23 : x ≠ (M.op y x) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b20e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b20e28
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e30 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e29
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : x = (k x y) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e88 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e31
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e31 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e98 : x = (M.op y x) ∨ y = (M.op x x) := by grind
            clear b20e88
            have b20e102 : y = (M.op x x) := by
              first
              | (have r₁ := b20e98
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e98 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e98
            have b20e105 : False := by grind
            exact b20e105
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b21e23 : x ≠ (M.op y x) := by grind
            have b21e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b21e14 y y x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e40 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 (M.op x y) X1
                 have i₂ := b21e31 (M.op X0 (M.op x y))
                 grind)
              | exact superpose b21e31 b21e14
              | exact resolve b21e14 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e41 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b21e40 x X1
                 have i₂ := b21e31 x
                 grind)
              | exact superpose b21e31 b21e40
              | exact resolve b21e40 b21e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e31 b21e40
            have b21e53 : x ≠ x := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e41 y
                 grind)
              | exact superpose b21e41 b21e23
              | (have r₁ := b21e23
                 have r₂ := b21e41 y
                 grind)
              | exact resolve b21e23 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e41
            have b21e59 : False := by grind
            exact b21e59
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : x ≠ (M.op y x) := by grind
              have b22e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e34 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
                intro X0
                first
                | (have i₁ := b22e15 (σ y) (σ x) x
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e15
                | exact resolve b22e15 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b22e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b22e36 X0 X1 x X3
                   have i₂ := b22e15 X0 X1 x
                   grind)
                | exact superpose b22e15 b22e36
                | exact resolve b22e36 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e36
              have b22e91 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b22e38 (σ y) (σ x) x
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e38
                | exact resolve b22e38 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e147 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by grind
              clear b22e34
              have b22e155 : (σ x) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b22e147
                   have i₂ := b22e91 (σ x)
                   grind)
                | exact superpose b22e91 b22e147
                | exact resolve b22e147 b22e91
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e91 b22e147
              have b22e157 : (σ x) = (σ (k x x)) := by
                first
                | (have i₁ := b22e155
                   have i₂ := b22e21 x x
                   grind)
                | exact superpose b22e21 b22e155
                | exact resolve b22e155 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e155
              have b22e259 : (k x x) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x x)
                   have i₂ := b22e157
                   grind)
                | exact superpose b22e157 b22e16
                | exact resolve b22e16 b22e157
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e157
              have b22e262 : x = (k x x) := by
                first
                | (have i₁ := b22e259
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e259
                | exact resolve b22e259 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e259
              have b22e270 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b22e20 x x
                   have i₂ := b22e262
                   grind)
                | exact superpose b22e262 b22e20
                | (have j0 := b22e20 x x
                   grind)
                | exact resolve b22e20 b22e262
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e262
              have b22e271 : x = (M.op x x) := by grind
              clear b22e270
              have b22e327 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b22e38 x x x
                   have i₂ := b22e271
                   grind)
                | exact superpose b22e271 b22e38
                | exact resolve b22e38 b22e271
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e38 b22e271
              have b22e431 : x ≠ x := by
                first
                | (have i₁ := b22e24
                   have i₂ := b22e327 y
                   grind)
                | exact superpose b22e327 b22e24
                | (have r₁ := b22e24
                   have r₂ := b22e327 y
                   grind)
                | exact resolve b22e24 b22e327
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e327
              have b22e442 : False := by grind
              exact b22e442
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op x x) := by grind
              have b23e24 : x ≠ (M.op y x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b23e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b23e34 X0 X1 x X3
                   have i₂ := b23e15 X0 X1 x
                   grind)
                | exact superpose b23e15 b23e34
                | exact resolve b23e34 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34
              have b23e48 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e52 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
              clear b23e48
              have b23e55 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e52
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e52 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e52
              have b23e57 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e55
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e55
                | exact resolve b23e55 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e55
              have b23e61 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e57
                   grind)
                | exact superpose b23e57 b23e16
                | exact resolve b23e16 b23e57
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e57
              have b23e62 : y = (k x y) := by
                first
                | (have i₁ := b23e61
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e61
                | exact resolve b23e61 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e61
              have b23e82 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e62
                   grind)
                | exact superpose b23e62 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e62
              have b23e83 : y = (M.op y x) ∨ x = (M.op y x) := by
                first
                | (have r₁ := b23e82
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e82 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e82
              have b23e85 : y = (M.op y x) := by
                first
                | (have r₁ := b23e83
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e83 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e83
              have b23e96 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b23e36 y x x
                   have i₂ := b23e85
                   grind)
                | exact superpose b23e85 b23e36
                | exact resolve b23e36 b23e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36 b23e85
              have b23e126 : y ≠ y := by
                first
                | (have i₁ := b23e28
                   have i₂ := b23e96 x
                   grind)
                | exact superpose b23e96 b23e28
                | (have r₁ := b23e28
                   have r₂ := b23e96 x
                   grind)
                | exact resolve b23e28 b23e96
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e96
              have b23e133 : False := by grind
              exact b23e133
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X2
              grind
            have b24e23 : x ≠ (M.op y x) := by grind
            have b24e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e31 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b24e14 y y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e39 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X0 (M.op x y) X1
                 have i₂ := b24e31 (M.op X0 (M.op x y))
                 grind)
              | exact superpose b24e31 b24e14
              | exact resolve b24e14 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e40 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b24e39 x X1
                 have i₂ := b24e31 x
                 grind)
              | exact superpose b24e31 b24e39
              | exact resolve b24e39 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e39
            have b24e48 : x ≠ x := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e40 y
                 grind)
              | exact superpose b24e40 b24e23
              | (have r₁ := b24e23
                 have r₂ := b24e40 y
                 grind)
              | exact resolve b24e23 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e40
            have b24e54 : False := by grind
            exact b24e54
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e22
                | exact resolve b25e22 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e33 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
                intro X0
                first
                | (have i₁ := b25e15 x y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b25e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e35 X0 X1 x X3
                   have i₂ := b25e15 X0 X1 x
                   grind)
                | exact superpose b25e15 b25e35
                | exact resolve b25e35 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e41 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 (M.op y y) X1
                   have i₂ := b25e33 (M.op X0 (M.op y y))
                   grind)
                | exact superpose b25e33 b25e15
                | exact resolve b25e15 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e42 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b25e41 x X1
                   have i₂ := b25e33 x
                   grind)
                | exact superpose b25e33 b25e41
                | exact resolve b25e41 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33 b25e41
              have b25e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e69 : y = (k y y) := by grind
              clear b25e42
              have b25e347 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b25e58 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e58
              have b25e349 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b25e347 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e347
              have b25e996 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e349 y
                   have i₂ := b25e69
                   grind)
                | exact superpose b25e69 b25e349
                | (have j0 := b25e349 y
                   grind)
                | exact resolve b25e349 b25e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e69 b25e349
              have b25e1000 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b25e996
              have b25e1049 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e37 (σ y) (σ y) x
                   have i₂ := b25e1000
                   grind)
                | exact superpose b25e1000 b25e37
                | exact resolve b25e37 b25e1000
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37 b25e1000
              have b25e1169 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b25e30
                   have i₂ := b25e1049 (σ x)
                   grind)
                | exact superpose b25e1049 b25e30
                | (have r₁ := b25e30
                   have r₂ := b25e1049 (σ x)
                   grind)
                | exact resolve b25e30 b25e1049
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30 b25e1049
              have b25e1188 : False := by grind
              exact b25e1188
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e24 : x ≠ (M.op y x) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X0 X1) X1) X3
                   have i₂ := b26e15 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e33 X0 X1 x X3
                   have i₂ := b26e15 X0 X1 x
                   grind)
                | exact superpose b26e15 b26e33
                | exact resolve b26e33 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e19 (M.op X0 X1) X2
                   have i₂ := b26e35 X0 X1 X2
                   grind)
                | exact superpose b26e35 b26e19
                | (have j0 := b26e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e19 (M.op X0 X1) x
                   have r₂ := b26e35 X0 X1 x
                   grind)
                | exact resolve b26e19 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e48 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e47 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e47
              have b26e49 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e48 X0 X1 X2
                   have i₂ := b26e35 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e35 b26e48
                | (have j0 := b26e48 X0 X1 X2
                   grind)
                | exact resolve b26e48 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e48
              have b26e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b26e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e72 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 X0 X0 x
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e35 X0 X1 x
                   have i₂ := b26e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b26e20 b26e35
                | (have j1 := b26e20 X1 X0
                   grind)
                | exact resolve b26e35 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e79 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                grind
              clear b26e30
              have b26e84 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e79 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e79
                | exact resolve b26e79 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79
              have b26e131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e69 (σ X1) (σ X0)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e69
                | (have j0 := b26e69 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e69 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e69
              have b26e224 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (σ X1) (σ X1) x
                   have i₂ := b26e68 X0 X1
                   grind)
                | exact superpose b26e68 b26e35
                | (have j1 := b26e68 X0 X1
                   grind)
                | exact resolve b26e35 b26e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68
              have b26e362 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e84 (M.op X0 X1)
                   have i₂ := b26e49 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact superpose b26e49 b26e84
                | (have j1 := b26e49 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b26e84 b26e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49 b26e84
              have b26e364 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b26e362 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e362
              have b26e806 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X0 X2
                   have i₂ := b26e72 X0 X3 (M.op X1 X0)
                   grind)
                | exact superpose b26e72 b26e15
                | (have j1 := b26e72 X0 X3 X2
                   grind)
                | exact resolve b26e15 b26e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1783 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e131 y x
                   grind)
                | exact superpose b26e131 b26e22
                | (have j1 := b26e131 y x
                   grind)
                | exact resolve b26e22 b26e131
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e131
              have b26e1857 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b26e364 X0 X1
                   grind)
                | exact superpose b26e364 b26e16
                | exact resolve b26e16 b26e364
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e364
              have b26e1985 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e224 x X0 (σ y)
                   grind)
                | exact superpose b26e224 b26e26
                | (have j1 := b26e224 x X0 x
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e224 x x (σ y)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e224 y x x
                   grind)
                | exact resolve b26e26 b26e224
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e224
              have b26e2004 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e1985 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1985
              have b26e4380 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b26e1857 X0 X1
                   grind)
                | exact superpose b26e1857 b26e35
                | exact resolve b26e35 b26e1857
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e1857
              have b26e13275 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2004 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2004
              have b26e14275 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e24
                   have i₂ := b26e806 x y X0 X1
                   grind)
                | (have i₁ := b26e24
                   have i₂ := b26e806 x X0 y X1
                   grind)
                | exact superpose b26e806 b26e24
                | (have j1 := b26e806 x X1 x X1
                   grind)
                | (have r₁ := b26e24
                   have r₂ := b26e806 y X1 x x
                   grind)
                | exact resolve b26e24 b26e806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e806
              have b26e14440 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X1
                first
                | (have j0 := b26e14275 x X1
                   have j1 := b26e72 x X1 x
                   grind)
                | (have r₁ := b26e14275 x X1
                   have r₂ := b26e72 x X1 x
                   grind)
                | (have r₁ := b26e14275 x X1
                   have r₂ := b26e72 x x x
                   grind)
                | exact resolve b26e14275 b26e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72 b26e14275
              have b26e22816 : ∀ X0 : G, (σ X0) ≠ (σ (M.op x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (M.op x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e13275 X0
                   have i₂ := b26e14440 X0
                   grind)
                | exact superpose b26e14440 b26e13275
                | (have j0 := b26e13275 X0
                   have j1 := b26e14440 X0
                   grind)
                | exact resolve b26e13275 b26e14440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e13275
              have b26e48444 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e1783
                   have i₂ := b26e14440 y
                   grind)
                | exact superpose b26e14440 b26e1783
                | (have j1 := b26e14440 y
                   grind)
                | exact resolve b26e1783 b26e14440
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1783 b26e14440
              have b26e48474 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
              clear b26e48444
              have b26e48490 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have j1 := b26e22816 y
                   grind)
                | (have r₁ := b26e48474
                   have r₂ := b26e22816 y
                   grind)
                | exact resolve b26e48474 b26e22816
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e22816 b26e48474
              have b26e48503 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e48490
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e48490 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e48490
              have b26e48547 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
                intro X0
                first
                | (have i₁ := b26e4380 (σ x) (σ y) x
                   have i₂ := b26e48503
                   grind)
                | exact superpose b26e48503 b26e4380
                | exact resolve b26e4380 b26e48503
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4380 b26e48503
              have b26e48560 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e48547 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e48547
                | exact resolve b26e48547 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e48547
              have b26e48621 : y ≠ y := by
                first
                | (have i₁ := b26e28
                   have i₂ := b26e48560 x
                   grind)
                | exact superpose b26e48560 b26e28
                | (have r₁ := b26e28
                   have r₂ := b26e48560 x
                   grind)
                | exact resolve b26e28 b26e48560
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e48560
              have b26e48669 : False := by grind
              exact b26e48669
