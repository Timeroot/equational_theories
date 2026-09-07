import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pxy_Equation887 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e11 y x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
           have i₂ := b0e11 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : y = (M.op x y) := by
        first
        | (have i₁ := b0e35 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X0 X1) X2
           have i₂ := b0e35 X0 X1
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e73 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op y (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x (M.op y (M.op X0 X0)) X1
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e76 : ∀ X0 : G, x = (M.op X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e73 X0 x
           have i₂ := b0e43 y (M.op X0 X0) x
           grind)
        | exact superpose b0e43 b0e73
        | exact resolve b0e73 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73
      have b0e86 : ∀ X0 : G, (M.op X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 X0 X0
           have i₂ := b0e76 (M.op X0 X0)
           grind)
        | exact superpose b0e76 b0e11
        | exact resolve b0e11 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e99 : ∀ X0 : G, (M.op x X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 X0 x
           have i₂ := b0e86 X0
           grind)
        | exact superpose b0e86 b0e35
        | exact resolve b0e35 b0e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e86
      have b0e111 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) (M.op (σ y) (M.op X0 X0)) X1
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e114 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e111 X0 x
           have i₂ := b0e43 (σ y) (M.op X0 X0) x
           grind)
        | exact superpose b0e43 b0e111
        | exact resolve b0e111 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e111
      have b0e121 : x = (σ x) := by
        first
        | (have i₁ := b0e114 x
           have i₂ := b0e76 x
           grind)
        | exact superpose b0e76 b0e114
        | exact resolve b0e114 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76 b0e114
      have b0e128 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e121
           grind)
        | exact superpose b0e121 b0e18
        | exact resolve b0e18 b0e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e121
      have b0e134 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e128
           have i₂ := b0e99 (σ y)
           grind)
        | exact superpose b0e99 b0e128
        | exact resolve b0e128 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99 b0e128
      have b0e137 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e134
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e134
        | exact resolve b0e134 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e134
      have b0e138 : False := by grind
      exact b0e138
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b1e24 : y ≠ y ∨ x = (k x y) := by
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
        have b1e26 : x = (k x y) := by grind
        clear b1e24
        have b1e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e44
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e23
             grind)
          | exact resolve b1e47 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e52 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e51
          | exact resolve b1e51 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e51
        have b1e53 : False := by grind
        exact b1e53
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e12 y x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
             have i₂ := b2e12 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (M.op X0 X1) X2
             have i₂ := b2e29 X0 X1
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e65 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op y (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 x (M.op y (M.op X0 X0)) X1
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e68 : ∀ X0 : G, x = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e65 X0 x
             have i₂ := b2e36 y (M.op X0 X0) x
             grind)
          | exact superpose b2e36 b2e65
          | exact resolve b2e65 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e65
        have b2e78 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 X0 X0
             have i₂ := b2e68 (M.op X0 X0)
             grind)
          | exact superpose b2e68 b2e12
          | exact resolve b2e12 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 : G, X0 ≠ X0 ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e78 X0
             grind)
          | exact superpose b2e78 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x X0
             have r₂ := b2e78 X0
             grind)
          | exact resolve b2e15 b2e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e90 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e89 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e298 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e53 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e301 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e298 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298
        have b2e313 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = x := by
          intro X0
          first
          | (have i₁ := b2e301 X0
             have i₂ := b2e68 (σ X0)
             grind)
          | exact superpose b2e68 b2e301
          | (have j0 := b2e301 X0
             grind)
          | exact resolve b2e301 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e301
        have b2e537 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
          first
          | (have i₁ := b2e313 x
             have i₂ := b2e90 x
             grind)
          | exact superpose b2e90 b2e313
          | (have j0 := b2e313 x
             grind)
          | exact resolve b2e313 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90 b2e313
        have b2e540 : x = (σ x) := by grind
        clear b2e537
        have b2e555 : (σ y) ≠ (M.op (σ y) x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e540
             grind)
          | exact superpose b2e540 b2e21
          | exact resolve b2e21 b2e540
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e540
        have b2e569 : False := by grind
        exact b2e569
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b3e25 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e25
        have b3e27 : (σ x) = (σ (k x y)) := by
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
        have b3e28 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e13
          | exact resolve b3e13 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e29 : x = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e55 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e58 : x = y ∨ y = (k x y) := by grind
        clear b3e55
        have b3e60 : y = (k x y) := by
          first
          | (have r₁ := b3e58
             have r₂ := b3e23
             grind)
          | exact resolve b3e58 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : x = y := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e29
          | exact resolve b3e29 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e60
        have b3e65 : False := by grind
        exact b3e65
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b4e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : y = (M.op x x) := by
            first
            | (have i₁ := b4e34 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e34
            | exact resolve b4e34 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e34 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X1 X1) X1
               have i₂ := b4e34 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X0 X1) X2
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e62 : x = (M.op x y) := by
            first
            | (have i₁ := b4e34 x x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e34
            | exact resolve b4e34 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e128 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e41 X0 x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e41
            | exact resolve b4e41 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e41
          have b4e152 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 x y X0 X1
               have i₂ := b4e62
               grind)
            | exact superpose b4e62 b4e33
            | exact resolve b4e33 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e62
          have b4e196 : ∀ X0 : G, y = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e152 X0 x
               have i₂ := b4e42 x (M.op X0 X0) x
               grind)
            | exact superpose b4e42 b4e152
            | exact resolve b4e152 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e152
          have b4e428 : y = (σ y) := by
            first
            | (have i₁ := b4e196 (σ x)
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e196
            | exact resolve b4e196 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e196
          have b4e461 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e428
               grind)
            | exact superpose b4e428 b4e20
            | exact resolve b4e20 b4e428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428
          have b4e474 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e461
               have i₂ := b4e128 (σ x)
               grind)
            | exact superpose b4e128 b4e461
            | exact resolve b4e461 b4e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e461
          have b4e476 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e474
               have i₂ := b4e128 x
               grind)
            | exact superpose b4e128 b4e474
            | exact resolve b4e474 b4e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128 b4e474
          have b4e477 : False := by grind
          exact b4e477
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b5e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X1 (M.op X0 X1)
               have i₂ := b5e31 X0 X1
               grind)
            | exact superpose b5e31 b5e31
            | exact resolve b5e31 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e42 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e45 : x = y ∨ y = (k x y) := by grind
          clear b5e42
          have b5e47 : y = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e25
               grind)
            | exact resolve b5e45 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e45
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e243 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e51 x y
               grind)
            | exact superpose b5e51 b5e23
            | (have j1 := b5e51 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e51 x y
               grind)
            | exact resolve b5e23 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e256 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e243
          have b5e272 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e256
               have r₂ := b5e24
               grind)
            | exact resolve b5e256 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e256
          have b5e296 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e272
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e272
            | exact resolve b5e272 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e272
          have b5e392 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e35 (σ x) (σ y)
               have i₂ := b5e296
               grind)
            | exact superpose b5e296 b5e35
            | exact resolve b5e35 b5e296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e296
          have b5e401 : False := by grind
          exact b5e401
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e23
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
        have b6e40 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
             have i₂ := b6e12 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
        have b6e69 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e66
             have r₂ := b6e21
             grind)
          | exact resolve b6e66 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e72 : x = (M.op x y) := by
          first
          | (have r₁ := b6e69
             have r₂ := b6e20
             grind)
          | exact resolve b6e69 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e75 : x = (M.op y x) := by
          first
          | (have i₁ := b6e40 x y
             have i₂ := b6e72
             grind)
          | exact superpose b6e72 b6e40
          | exact resolve b6e40 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e72
        have b6e80 : False := by grind
        exact b6e80
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
          have b7e31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b7e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          clear b7e42
          have b7e47 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e25
               grind)
            | exact resolve b7e45 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e45
          have b7e49 : (σ y) = (σ (k x y)) := by
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
          have b7e52 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : y = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e62 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e63 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : y = (M.op x y) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e73 : x = (M.op y y) := by
            first
            | (have i₁ := b7e31 x y
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e31
            | exact resolve b7e31 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e88 : y = (M.op y x) := by
            first
            | (have i₁ := b7e31 y y
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e31
            | exact resolve b7e31 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e73
          have b7e93 : False := by grind
          exact b7e93
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e290 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e49 x y
               grind)
            | exact superpose b8e49 b8e23
            | (have j1 := b8e49 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e49 x y
               grind)
            | exact resolve b8e23 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e303 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b8e290
          have b8e322 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e303
               have r₂ := b8e24
               grind)
            | exact resolve b8e303 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e303
          have b8e354 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e322
               grind)
            | exact superpose b8e322 b8e20
            | exact resolve b8e20 b8e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322
          have b8e366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e354
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e354
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e354 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e354
          have b8e367 : x = (M.op y x) ∨ y = (M.op y x) := by grind
          clear b8e366
          have b8e368 : y = (M.op y x) := by
            first
            | (have r₁ := b8e367
               have r₂ := b8e22
               grind)
            | exact resolve b8e367 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e369 : False := by grind
          exact b8e369

/-- `Equation916`: `x = y ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_x_x_pyx_Equation916 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law916 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law916.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
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
      · have b1e12 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e37 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b1e12 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        clear b1e29
        have b1e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e69 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 X0
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op X0 X0) X1
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op X0 X0)
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e93 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e50 X1 X0
             have i₂ := b1e17 X1 (σ X0)
             grind)
          | exact superpose b1e17 b1e50
          | (have j1 := b1e17 X1 (σ X0)
             grind)
          | exact resolve b1e50 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e123 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ X0) X1
             have i₂ := b1e54 X0 X0
             grind)
          | exact superpose b1e54 b1e12
          | (have j1 := b1e54 X0 X0
             grind)
          | exact resolve b1e12 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e134 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e123 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123
        have b1e406 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b1e72 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b1e12 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
             grind)
          | exact superpose b1e12 b1e72
          | exact resolve b1e72 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e413 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e406 X0
             have i₂ := b1e12 X0 X0
             grind)
          | exact superpose b1e12 b1e406
          | exact resolve b1e406 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e406
        have b1e414 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e413 X0
             have i₂ := b1e37 (M.op X0 X0)
             grind)
          | exact superpose b1e37 b1e413
          | exact resolve b1e413 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e413
        have b1e415 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e414 X0
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e414
          | exact resolve b1e414 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e414
        have b1e416 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b1e415 (M.op X0 X0)
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e415
          | exact resolve b1e415 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e422 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b1e416 X0
             have i₂ := b1e415 X0
             grind)
          | exact superpose b1e415 b1e416
          | exact resolve b1e416 b1e415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e416
        have b1e423 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e73 (M.op X0 X0) X1
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e73
          | exact resolve b1e73 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e428 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b1e72 (M.op X0 (M.op X0 X0)) X0
             have i₂ := b1e73 X0 (M.op X0 (M.op X0 X0))
             grind)
          | exact superpose b1e73 b1e72
          | exact resolve b1e72 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e73
        have b1e434 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e428 X0
             have i₂ := b1e69 X0
             grind)
          | exact superpose b1e69 b1e428
          | exact resolve b1e428 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e428
        have b1e435 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e423 X0 X1
             have i₂ := b1e415 X0
             grind)
          | exact superpose b1e415 b1e423
          | exact resolve b1e423 b1e415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e423
        have b1e505 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b1e434 X0
             grind)
          | exact superpose b1e434 b1e12
          | exact resolve b1e12 b1e434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e434
        have b1e728 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e69 X1
             have i₂ := b1e505 X1 X0
             grind)
          | exact superpose b1e505 b1e69
          | exact resolve b1e69 b1e505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e734 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e415 X1
             have i₂ := b1e505 X1 X0
             grind)
          | exact superpose b1e505 b1e415
          | exact resolve b1e415 b1e505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e779 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X1 X1) (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e134 (τ X0) X1
             have i₂ := b1e30 X0 (τ X0)
             grind)
          | exact superpose b1e30 b1e134
          | (have j0 := b1e134 (τ X0) X1
             grind)
          | exact resolve b1e134 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e134
        have b1e787 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e779 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e779
          | (have j0 := b1e779 X0 X1
             grind)
          | exact resolve b1e779 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e779
        have b1e791 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e787 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e787
          | (have j0 := b1e787 X0 X1
             grind)
          | exact resolve b1e787 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e787
        have b1e798 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e728 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b1e435 X0 X0
             grind)
          | exact superpose b1e435 b1e728
          | exact resolve b1e728 b1e435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e728
        have b1e2237 : (σ x) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) := by
          first
          | (have i₁ := b1e798 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e798
          | exact resolve b1e798 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2244 : y = (M.op y (M.op (M.op x (M.op x x)) x)) := by
          first
          | (have i₁ := b1e798 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e798
          | exact resolve b1e798 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e798
        have b1e2268 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b1e2244
             have i₂ := b1e422 x
             grind)
          | exact superpose b1e422 b1e2244
          | exact resolve b1e2244 b1e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2244
        have b1e2270 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e2237
             have i₂ := b1e422 (σ y)
             grind)
          | exact superpose b1e422 b1e2237
          | exact resolve b1e2237 b1e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2237
        have b1e2388 : x = (M.op (M.op y (M.op y y)) y) := by
          first
          | (have i₁ := b1e435 y x
             have i₂ := b1e2268
             grind)
          | exact superpose b1e2268 b1e435
          | exact resolve b1e435 b1e2268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2268
        have b1e2396 : x = (M.op y y) := by
          first
          | (have i₁ := b1e2388
             have i₂ := b1e422 y
             grind)
          | exact superpose b1e422 b1e2388
          | exact resolve b1e2388 b1e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2388
        have b1e2501 : (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b1e37 y
             have i₂ := b1e2396
             grind)
          | exact superpose b1e2396 b1e37
          | exact resolve b1e37 b1e2396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e2513 : y = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b1e415 y
             have i₂ := b1e2396
             grind)
          | exact superpose b1e2396 b1e415
          | exact resolve b1e415 b1e2396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e415
        have b1e2518 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e505 X0 y
             have i₂ := b1e2396
             grind)
          | exact superpose b1e2396 b1e505
          | exact resolve b1e505 b1e2396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2523 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e734 y X0
             have i₂ := b1e2396
             grind)
          | exact superpose b1e2396 b1e734
          | exact resolve b1e734 b1e2396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e734 b1e2396
        have b1e5356 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) := by
          first
          | (have i₁ := b1e435 (σ x) (σ y)
             have i₂ := b1e2270
             grind)
          | exact superpose b1e2270 b1e435
          | exact resolve b1e435 b1e2270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e435 b1e2270
        have b1e5365 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e5356
             have i₂ := b1e422 (σ x)
             grind)
          | exact superpose b1e422 b1e5356
          | exact resolve b1e5356 b1e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422 b1e5356
        have b1e8682 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e93 x (σ x)
             have i₂ := b1e5365
             grind)
          | exact superpose b1e5365 b1e93
          | exact resolve b1e93 b1e5365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93 b1e5365
        have b1e8742 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) := by grind
        clear b1e8682
        have b1e8756 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8742
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e8742
          | exact resolve b1e8742 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8742
        have b1e8766 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8756
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e8756
          | exact resolve b1e8756 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8756
        have b1e8782 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 X0) y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e791 x X0
             have i₂ := b1e8766
             grind)
          | exact superpose b1e8766 b1e791
          | (have j0 := b1e791 x x
             grind)
          | exact resolve b1e791 b1e8766
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e791 b1e8766
        have b1e8801 : x = (M.op y (M.op y y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8782 x
             have i₂ := b1e505 y x
             grind)
          | exact superpose b1e505 b1e8782
          | exact resolve b1e8782 b1e505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e505 b1e8782
        have b1e8802 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8801
             have i₂ := b1e2518 y
             grind)
          | exact superpose b1e2518 b1e8801
          | exact resolve b1e8801 b1e2518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2518 b1e8801
        have b1e8803 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8802
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e8802
          | exact resolve b1e8802 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8802
        have b1e8804 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e8803
             have i₂ := b1e2501
             grind)
          | exact superpose b1e2501 b1e8803
          | exact resolve b1e8803 b1e2501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2501 b1e8803
        have b1e8805 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b1e8804
        have b1e8961 : x = (M.op x (M.op y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e2523 x
             have i₂ := b1e8805
             grind)
          | exact superpose b1e8805 b1e2523
          | exact resolve b1e2523 b1e8805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2523 b1e8805
        have b1e8969 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e8961
             have i₂ := b1e2513
             grind)
          | exact superpose b1e2513 b1e8961
          | exact resolve b1e8961 b1e2513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2513 b1e8961
        have b1e9091 : y = (τ (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e8969
             grind)
          | exact superpose b1e8969 b1e13
          | exact resolve b1e13 b1e8969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8969
        have b1e9158 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e9091
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e9091
          | exact resolve b1e9091 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9091
        have b1e9159 : x = y := by grind
        clear b1e9158
        have b1e9403 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e9159
             grind)
          | exact superpose b1e9159 b1e21
          | exact resolve b1e21 b1e9159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e9404 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e9159
             grind)
          | exact superpose b1e9159 b1e22
          | exact resolve b1e22 b1e9159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9159
        have b1e9450 : False := by grind
        exact b1e9450
      · have b2e12 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
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
        have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e32 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b2e12 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e42 : x ≠ x ∨ y = (M.op y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : y = (M.op y x) ∨ y = (k y x) := by grind
        clear b2e42
        have b2e46 : y = (k y x) := by
          first
          | (have j1 := b2e15 y x
             grind)
          | (have r₁ := b2e44
             have r₂ := b2e15 y x
             grind)
          | exact resolve b2e44 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e51 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e65 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 X0
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op X0 X0) X1
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e69 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op X0 X0)
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e119 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (σ X0) X1
             have i₂ := b2e51 X0 X0
             grind)
          | exact superpose b2e51 b2e12
          | (have j1 := b2e51 X0 X0
             grind)
          | exact resolve b2e12 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e121 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e51 x y
             grind)
          | exact superpose b2e51 b2e22
          | (have j1 := b2e51 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e51 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e51 y x
             grind)
          | exact resolve b2e22 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e122 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X1) (σ X0)
             have i₂ := b2e51 X1 X0
             grind)
          | exact superpose b2e51 b2e16
          | (have j0 := b2e16 (σ X1) (σ X0)
             have j1 := b2e51 X1 X0
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e51 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e51 X0 X1
             grind)
          | exact resolve b2e16 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e128 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e122 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122
        have b2e129 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e128 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128
        have b2e130 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e121
        have b2e132 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e119 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119
        have b2e139 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e129 X0 X1
             have j1 := b2e15 (σ X1) (σ X0)
             grind)
          | (have r₁ := b2e129 X0 X1
             have r₂ := b2e15 (σ X1) (σ X0)
             grind)
          | exact resolve b2e129 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129
        have b2e140 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e130
             have r₂ := b2e21
             grind)
          | exact resolve b2e130 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130
        have b2e146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e139 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e139
          | (have j0 := b2e139 X0 X1
             grind)
          | exact resolve b2e139 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e147 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e140
             have i₂ := b2e46
             grind)
          | exact superpose b2e46 b2e140
          | exact resolve b2e140 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46 b2e140
        have b2e150 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e147
             grind)
          | exact superpose b2e147 b2e21
          | exact resolve b2e21 b2e147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e147
        have b2e324 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e68 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b2e12 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
             grind)
          | exact superpose b2e12 b2e68
          | exact resolve b2e68 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e331 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e324 X0
             have i₂ := b2e12 X0 X0
             grind)
          | exact superpose b2e12 b2e324
          | exact resolve b2e324 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e324
        have b2e332 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e331 X0
             have i₂ := b2e32 (M.op X0 X0)
             grind)
          | exact superpose b2e32 b2e331
          | exact resolve b2e331 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e331
        have b2e333 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e332 X0
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e332
          | exact resolve b2e332 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e332
        have b2e334 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b2e333 (M.op X0 X0)
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e333
          | exact resolve b2e333 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e340 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b2e334 X0
             have i₂ := b2e333 X0
             grind)
          | exact superpose b2e333 b2e334
          | exact resolve b2e334 b2e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e334
        have b2e341 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e69 (M.op X0 X0) X1
             have i₂ := b2e32 X0
             grind)
          | exact superpose b2e32 b2e69
          | exact resolve b2e69 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e346 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e68 (M.op X0 (M.op X0 X0)) X0
             have i₂ := b2e69 X0 (M.op X0 (M.op X0 X0))
             grind)
          | exact superpose b2e69 b2e68
          | exact resolve b2e68 b2e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e69
        have b2e352 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e346 X0
             have i₂ := b2e65 X0
             grind)
          | exact superpose b2e65 b2e346
          | exact resolve b2e346 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e346
        have b2e353 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e341 X0 X1
             have i₂ := b2e333 X0
             grind)
          | exact superpose b2e333 b2e341
          | exact resolve b2e341 b2e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e333 b2e341
        have b2e394 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (σ X0) X1
             have i₂ := b2e146 X0 X0
             grind)
          | exact superpose b2e146 b2e12
          | (have j1 := b2e146 X0 X0
             grind)
          | exact resolve b2e12 b2e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e146
        have b2e418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b2e352 X0
             grind)
          | exact superpose b2e352 b2e12
          | exact resolve b2e12 b2e352
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e677 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X1 X1) (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e132 (τ X0) X1
             have i₂ := b2e27 X0 (τ X0)
             grind)
          | exact superpose b2e27 b2e132
          | (have j0 := b2e132 (τ X0) X1
             grind)
          | exact resolve b2e132 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e132
        have b2e683 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e677 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e677
          | (have j0 := b2e677 X0 X1
             grind)
          | exact resolve b2e677 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e677
        have b2e687 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e683 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e683
          | (have j0 := b2e683 X0 X1
             grind)
          | exact resolve b2e683 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e683
        have b2e709 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e65 X1
             have i₂ := b2e418 X1 X0
             grind)
          | exact superpose b2e418 b2e65
          | exact resolve b2e65 b2e418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e793 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e709 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b2e353 X0 X0
             grind)
          | exact superpose b2e353 b2e709
          | exact resolve b2e709 b2e353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2272 : y = (M.op y (M.op (M.op x (M.op x x)) x)) := by
          first
          | (have i₁ := b2e793 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e793
          | exact resolve b2e793 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2296 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b2e2272
             have i₂ := b2e340 x
             grind)
          | exact superpose b2e340 b2e2272
          | exact resolve b2e2272 b2e340
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2272
        have b2e2431 : x = (M.op (M.op y (M.op y y)) y) := by
          first
          | (have i₁ := b2e353 y x
             have i₂ := b2e2296
             grind)
          | exact superpose b2e2296 b2e353
          | exact resolve b2e353 b2e2296
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e353 b2e2296
        have b2e2439 : x = (M.op y y) := by
          first
          | (have i₁ := b2e2431
             have i₂ := b2e340 y
             grind)
          | exact superpose b2e340 b2e2431
          | exact resolve b2e2431 b2e340
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2431
        have b2e2591 : (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b2e32 y
             have i₂ := b2e2439
             grind)
          | exact superpose b2e2439 b2e32
          | exact resolve b2e32 b2e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2604 : x = (M.op (M.op y x) y) := by
          first
          | (have i₁ := b2e340 y
             have i₂ := b2e2439
             grind)
          | exact superpose b2e2439 b2e340
          | exact resolve b2e340 b2e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e340
        have b2e2605 : y = (M.op (M.op y x) (M.op y x)) := by
          first
          | (have i₁ := b2e352 y
             have i₂ := b2e2439
             grind)
          | exact superpose b2e2439 b2e352
          | exact resolve b2e352 b2e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352
        have b2e2608 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e418 X0 y
             have i₂ := b2e2439
             grind)
          | exact superpose b2e2439 b2e418
          | exact resolve b2e418 b2e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2610 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e709 y X0
             have i₂ := b2e2439
             grind)
          | exact superpose b2e2439 b2e709
          | exact resolve b2e709 b2e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2820 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e709 x (k X0 X0)
             have i₂ := b2e687 X0 x
             grind)
          | exact superpose b2e687 b2e709
          | (have j1 := b2e687 X0 x
             grind)
          | exact resolve b2e709 b2e687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e687 b2e709
        have b2e2987 : x = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b2e2604
             have i₂ := b2e2591
             grind)
          | exact superpose b2e2591 b2e2604
          | exact resolve b2e2604 b2e2591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2604
        have b2e4205 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op y x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e418 X0 (M.op y x)
             have i₂ := b2e2605
             grind)
          | exact superpose b2e2605 b2e418
          | exact resolve b2e418 b2e2605
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2605
        have b2e4237 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e4205 X0
             have i₂ := b2e2591
             grind)
          | exact superpose b2e2591 b2e4205
          | exact resolve b2e4205 b2e2591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2591 b2e4205
        have b2e6551 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) X0)) = (M.op y (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e418 X0 X1
             have i₂ := b2e2608 X0
             grind)
          | exact superpose b2e2608 b2e418
          | exact resolve b2e418 b2e2608
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e418
        have b2e11377 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x x) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e2608 X0
             have i₂ := b2e4237 X0
             grind)
          | exact superpose b2e4237 b2e2608
          | exact resolve b2e2608 b2e4237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2608 b2e4237
        have b2e13701 : ∀ X0 X1 : G, (M.op y (M.op x (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0))) = (M.op X1 (M.op y (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e6551 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) X1
             have i₂ := b2e6551 X0 (M.op X1 X1)
             grind)
          | exact superpose b2e6551 b2e6551
          | exact resolve b2e6551 b2e6551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e13844 : ∀ X0 X1 : G, (M.op y (M.op x (M.op (M.op X1 (M.op X1 X1)) X0))) = (M.op X1 (M.op y (M.op x X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13701 X0 X1
             have i₂ := b2e32 X1
             grind)
          | exact superpose b2e32 b2e13701
          | exact resolve b2e13701 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e13701
        have b2e19563 : ∀ X0 : G, (M.op (M.op x x) y) = (M.op y (M.op x (M.op (M.op X0 (M.op X0 X0)) (M.op X0 y)))) := by
          intro X0
          first
          | (have i₁ := b2e11377 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 y))
             have i₂ := b2e793 X0 y
             grind)
          | exact superpose b2e793 b2e11377
          | exact resolve b2e11377 b2e793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e793 b2e11377
        have b2e19646 : ∀ X0 : G, (M.op (M.op x x) y) = (M.op X0 (M.op y (M.op x (M.op X0 y)))) := by
          intro X0
          first
          | (have i₁ := b2e19563 X0
             have i₂ := b2e13844 (M.op X0 y) X0
             grind)
          | exact superpose b2e13844 b2e19563
          | exact resolve b2e19563 b2e13844
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13844 b2e19563
        have b2e19670 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op x (M.op X0 y)))) := by
          intro X0
          first
          | (have i₁ := b2e19646 X0
             have i₂ := b2e2987
             grind)
          | exact superpose b2e2987 b2e19646
          | exact resolve b2e19646 b2e2987
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2987 b2e19646
        have b2e28723 : x = (M.op (k y y) (M.op y (M.op x (k y y)))) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e19670 (k y y)
             have i₂ := b2e2820 y
             grind)
          | exact superpose b2e2820 b2e19670
          | (have j1 := b2e2820 y
             grind)
          | exact resolve b2e19670 b2e2820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2820 b2e19670
        have b2e28731 : x = (k y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e28723
             have i₂ := b2e2610 (k y y)
             grind)
          | exact superpose b2e2610 b2e28723
          | exact resolve b2e28723 b2e2610
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28723
        have b2e28741 : x = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e28731
             have i₂ := b2e2439
             grind)
          | exact superpose b2e2439 b2e28731
          | exact resolve b2e28731 b2e2439
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2439 b2e28731
        have b2e28850 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 X0) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e394 y x
             have i₂ := b2e28741
             grind)
          | exact superpose b2e28741 b2e394
          | exact resolve b2e394 b2e28741
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e394 b2e28741
        have b2e28913 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op X0 X0) (σ x))) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e28850 X0
             grind)
          | (have r₁ := b2e28850 X0
             have r₂ := b2e150
             grind)
          | exact resolve b2e28850 b2e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28850
        have b2e28920 : (σ y) = (M.op y (M.op x (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e28913 x
             have i₂ := b2e6551 (σ x) x
             grind)
          | exact superpose b2e6551 b2e28913
          | exact resolve b2e28913 b2e6551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6551 b2e28913
        have b2e29227 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e2610 (σ x)
             have i₂ := b2e28920
             grind)
          | exact superpose b2e28920 b2e2610
          | exact resolve b2e2610 b2e28920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2610 b2e28920
        have b2e29266 : x = y := by
          first
          | (have r₁ := b2e29227
             have r₂ := b2e21
             grind)
          | exact resolve b2e29227 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29227
        have b2e29554 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e150
             have i₂ := b2e29266
             grind)
          | exact superpose b2e29266 b2e150
          | exact resolve b2e150 b2e29266
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150 b2e29266
        have b2e29615 : False := by grind
        exact b2e29615
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
        have b3e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e31 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b3e12 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X1 X0
             have i₂ := b3e17 (τ X1) X0
             grind)
          | exact superpose b3e17 b3e29
          | (have j1 := b3e17 (τ X1) X0
             grind)
          | exact resolve b3e29 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e29 X0 X1
             grind)
          | exact superpose b3e29 b3e13
          | exact resolve b3e13 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e72 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e58 X1 X0
             have i₂ := b3e17 X1 (σ X0)
             grind)
          | exact superpose b3e17 b3e58
          | (have j1 := b3e17 X1 (σ X0)
             grind)
          | exact resolve b3e58 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e80 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 X0
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e12
          | exact resolve b3e12 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e83 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X0 X0) X1
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e12
          | exact resolve b3e12 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 (M.op X0 X0)
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e12
          | exact resolve b3e12 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e434 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e83 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b3e12 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
             grind)
          | exact superpose b3e12 b3e83
          | exact resolve b3e83 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e441 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e434 X0
             have i₂ := b3e12 X0 X0
             grind)
          | exact superpose b3e12 b3e434
          | exact resolve b3e434 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e434
        have b3e442 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e441 X0
             have i₂ := b3e31 (M.op X0 X0)
             grind)
          | exact superpose b3e31 b3e441
          | exact resolve b3e441 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e441
        have b3e443 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e442 X0
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e442
          | exact resolve b3e442 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e442
        have b3e444 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b3e443 (M.op X0 X0)
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e443
          | exact resolve b3e443 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e450 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b3e444 X0
             have i₂ := b3e443 X0
             grind)
          | exact superpose b3e443 b3e444
          | exact resolve b3e444 b3e443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e444
        have b3e451 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e84 (M.op X0 X0) X1
             have i₂ := b3e31 X0
             grind)
          | exact superpose b3e31 b3e84
          | exact resolve b3e84 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e456 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e83 (M.op X0 (M.op X0 X0)) X0
             have i₂ := b3e84 X0 (M.op X0 (M.op X0 X0))
             grind)
          | exact superpose b3e84 b3e83
          | exact resolve b3e83 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83 b3e84
        have b3e462 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e456 X0
             have i₂ := b3e80 X0
             grind)
          | exact superpose b3e80 b3e456
          | exact resolve b3e456 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e456
        have b3e463 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e451 X0 X1
             have i₂ := b3e443 X0
             grind)
          | exact superpose b3e443 b3e451
          | exact resolve b3e451 b3e443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e443 b3e451
        have b3e533 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b3e462 X0
             grind)
          | exact superpose b3e462 b3e12
          | exact resolve b3e12 b3e462
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e462
        have b3e691 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e80 X1
             have i₂ := b3e533 X1 X0
             grind)
          | exact superpose b3e533 b3e80
          | exact resolve b3e80 b3e533
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e533
        have b3e769 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e691 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b3e463 X0 X0
             grind)
          | exact superpose b3e463 b3e691
          | exact resolve b3e691 b3e463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e691
        have b3e854 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e55 X0 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e55
          | exact resolve b3e55 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e887 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e854 X0 X1
             have i₂ := b3e18 X0 X1
             grind)
          | exact superpose b3e18 b3e854
          | (have j0 := b3e854 X0 X1
             grind)
          | exact resolve b3e854 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e854
        have b3e2158 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x))) := by
          first
          | (have i₁ := b3e769 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e769
          | exact resolve b3e769 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2165 : x = (M.op x (M.op (M.op y (M.op y y)) y)) := by
          first
          | (have i₁ := b3e769 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e769
          | exact resolve b3e769 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e769
        have b3e2189 : x = (M.op x (M.op y y)) := by
          first
          | (have i₁ := b3e2165
             have i₂ := b3e450 y
             grind)
          | exact superpose b3e450 b3e2165
          | exact resolve b3e2165 b3e450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2165
        have b3e2191 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e2158
             have i₂ := b3e450 (σ x)
             grind)
          | exact superpose b3e450 b3e2158
          | exact resolve b3e2158 b3e450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2158
        have b3e2300 : y = (M.op (M.op x (M.op x x)) x) := by
          first
          | (have i₁ := b3e463 x y
             have i₂ := b3e2189
             grind)
          | exact superpose b3e2189 b3e463
          | exact resolve b3e463 b3e2189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2189
        have b3e2308 : y = (M.op x x) := by
          first
          | (have i₁ := b3e2300
             have i₂ := b3e450 x
             grind)
          | exact superpose b3e450 b3e2300
          | exact resolve b3e2300 b3e450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2300
        have b3e2395 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b3e31 x
             have i₂ := b3e2308
             grind)
          | exact superpose b3e2308 b3e31
          | exact resolve b3e31 b3e2308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e2397 : x = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b3e80 x
             have i₂ := b3e2308
             grind)
          | exact superpose b3e2308 b3e80
          | exact resolve b3e80 b3e2308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e2308
        have b3e5176 : (σ x) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
          first
          | (have i₁ := b3e463 (σ y) (σ x)
             have i₂ := b3e2191
             grind)
          | exact superpose b3e2191 b3e463
          | exact resolve b3e463 b3e2191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e463 b3e2191
        have b3e5185 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e5176
             have i₂ := b3e450 (σ y)
             grind)
          | exact superpose b3e450 b3e5176
          | exact resolve b3e5176 b3e450
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e450 b3e5176
        have b3e8672 : (τ (σ x)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e72 y (σ y)
             have i₂ := b3e5185
             grind)
          | exact superpose b3e5185 b3e72
          | exact resolve b3e72 b3e5185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72 b3e5185
        have b3e8734 : (τ (σ x)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) := by grind
        clear b3e8672
        have b3e8748 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e8734
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e8734
          | exact resolve b3e8734 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8734
        have b3e8757 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e8748
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e8748
          | exact resolve b3e8748 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8748
        have b3e8780 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e887 y y
             have i₂ := b3e8757
             grind)
          | exact superpose b3e8757 b3e887
          | (have j0 := b3e887 y y
             grind)
          | exact resolve b3e887 b3e8757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e887 b3e8757
        have b3e8783 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b3e8780
        have b3e8791 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e8783
             have i₂ := b3e2395
             grind)
          | exact superpose b3e2395 b3e8783
          | exact resolve b3e8783 b3e2395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8783
        have b3e8798 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e8791
             have r₂ := b3e23
             grind)
          | exact resolve b3e8791 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e8791
        have b3e8802 : y = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e8798
             have i₂ := b3e2395
             grind)
          | exact superpose b3e2395 b3e8798
          | exact resolve b3e8798 b3e2395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2395 b3e8798
        have b3e8909 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2397
             have i₂ := b3e8802
             grind)
          | exact superpose b3e8802 b3e2397
          | exact resolve b3e2397 b3e8802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2397 b3e8802
        have b3e8935 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e8909
             have r₂ := b3e20
             grind)
          | exact resolve b3e8909 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8909
        have b3e9033 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e8935
             grind)
          | exact superpose b3e8935 b3e13
          | exact resolve b3e13 b3e8935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e8935
        have b3e9097 : x = y := by
          first
          | (have i₁ := b3e9033
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e9033
          | exact resolve b3e9033 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9033
        have b3e9344 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e9097
             grind)
          | exact superpose b3e9097 b3e20
          | exact resolve b3e20 b3e9097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e9345 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e9097
             grind)
          | exact superpose b3e9097 b3e21
          | exact resolve b3e21 b3e9097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9097
        have b3e9397 : False := by grind
        exact b3e9397
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e36 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op (M.op X0 X0) (M.op X0 X0)) X0
               have i₂ := b4e13 (M.op X0 X0) (M.op X0 X0)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 X0
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) X1
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0)
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e127 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1
               have i₂ := b4e59 X0 X0
               grind)
            | exact superpose b4e59 b4e13
            | (have j1 := b4e59 X0 X0
               grind)
            | exact resolve b4e13 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e129 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X1) (σ X0)
               have i₂ := b4e59 X1 X0
               grind)
            | exact superpose b4e59 b4e17
            | (have j0 := b4e17 (σ X1) (σ X0)
               have j1 := b4e59 X1 X0
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X1)
               have r₂ := b4e59 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X1) (σ X0)
               have r₂ := b4e59 X0 X1
               grind)
            | exact resolve b4e17 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e135 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e129 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129
          have b4e136 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e135 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e138 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e127 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127
          have b4e145 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e136 X0 X1
               have j1 := b4e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b4e136 X0 X1
               have r₂ := b4e16 (σ X1) (σ X0)
               grind)
            | exact resolve b4e136 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e145 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e145
            | (have j0 := b4e145 X0 X1
               grind)
            | exact resolve b4e145 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145
          have b4e399 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e76 (M.op (M.op X0 X0) (M.op X0 X0)) X0
               have i₂ := b4e13 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
               grind)
            | exact superpose b4e13 b4e76
            | exact resolve b4e76 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e406 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e399 X0
               have i₂ := b4e13 X0 X0
               grind)
            | exact superpose b4e13 b4e399
            | exact resolve b4e399 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e399
          have b4e407 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e406 X0
               have i₂ := b4e36 (M.op X0 X0)
               grind)
            | exact superpose b4e36 b4e406
            | exact resolve b4e406 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e406
          have b4e408 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e407 X0
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e407
            | exact resolve b4e407 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e407
          have b4e409 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e408 (M.op X0 X0)
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e408
            | exact resolve b4e408 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e415 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e409 X0
               have i₂ := b4e408 X0
               grind)
            | exact superpose b4e408 b4e409
            | exact resolve b4e409 b4e408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e409
          have b4e416 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e77 (M.op X0 X0) X1
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e77
            | exact resolve b4e77 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e421 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e76 (M.op X0 (M.op X0 X0)) X0
               have i₂ := b4e77 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b4e77 b4e76
            | exact resolve b4e76 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e77
          have b4e427 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e421 X0
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e421
            | exact resolve b4e421 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e421
          have b4e428 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e416 X0 X1
               have i₂ := b4e408 X0
               grind)
            | exact superpose b4e408 b4e416
            | exact resolve b4e416 b4e408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e416
          have b4e470 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 X1) (σ (k X0 X0)))) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1
               have i₂ := b4e152 X0 X0
               grind)
            | exact superpose b4e152 b4e13
            | (have j1 := b4e152 X0 X0
               grind)
            | exact resolve b4e13 b4e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152
          have b4e497 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b4e427 X0
               grind)
            | exact superpose b4e427 b4e13
            | exact resolve b4e13 b4e427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e655 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e73 X1
               have i₂ := b4e497 X1 X0
               grind)
            | exact superpose b4e497 b4e73
            | exact resolve b4e73 b4e497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e731 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e655 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b4e428 X0 X0
               grind)
            | exact superpose b4e428 b4e655
            | exact resolve b4e655 b4e428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e773 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X1 X1) (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e138 (τ X0) X1
               have i₂ := b4e31 X0 (τ X0)
               grind)
            | exact superpose b4e31 b4e138
            | (have j0 := b4e138 (τ X0) X1
               grind)
            | exact resolve b4e138 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e138
          have b4e784 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e773 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e773
            | (have j0 := b4e773 X0 X1
               grind)
            | exact resolve b4e773 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e773
          have b4e788 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e784 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e784
            | (have j0 := b4e784 X0 X1
               grind)
            | exact resolve b4e784 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e784
          have b4e2110 : (σ x) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) := by
            first
            | (have i₁ := b4e731 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e731
            | exact resolve b4e731 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2117 : x = (M.op x (M.op (M.op y (M.op y y)) y)) := by
            first
            | (have i₁ := b4e731 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e731
            | exact resolve b4e731 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2141 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b4e2117
               have i₂ := b4e415 y
               grind)
            | exact superpose b4e415 b4e2117
            | exact resolve b4e2117 b4e415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2117
          have b4e2143 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b4e2110
               have i₂ := b4e415 (σ y)
               grind)
            | exact superpose b4e415 b4e2110
            | exact resolve b4e2110 b4e415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2110
          have b4e2250 : y = (M.op (M.op x (M.op x x)) x) := by
            first
            | (have i₁ := b4e428 x y
               have i₂ := b4e2141
               grind)
            | exact superpose b4e2141 b4e428
            | exact resolve b4e428 b4e2141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2141
          have b4e2258 : y = (M.op x x) := by
            first
            | (have i₁ := b4e2250
               have i₂ := b4e415 x
               grind)
            | exact superpose b4e415 b4e2250
            | exact resolve b4e2250 b4e415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2250
          have b4e2343 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e36 x
               have i₂ := b4e2258
               grind)
            | exact superpose b4e2258 b4e36
            | exact resolve b4e36 b4e2258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2355 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b4e408 x
               have i₂ := b4e2258
               grind)
            | exact superpose b4e2258 b4e408
            | exact resolve b4e408 b4e2258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e408
          have b4e2357 : x = (M.op (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b4e427 x
               have i₂ := b4e2258
               grind)
            | exact superpose b4e2258 b4e427
            | exact resolve b4e427 b4e2258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e427
          have b4e2360 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e497 X0 x
               have i₂ := b4e2258
               grind)
            | exact superpose b4e2258 b4e497
            | exact resolve b4e497 b4e2258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2362 : ∀ X0 : G, (M.op X0 (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e655 x X0
               have i₂ := b4e2258
               grind)
            | exact superpose b4e2258 b4e655
            | exact resolve b4e655 b4e2258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2258
          have b4e2668 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e497 X0 y
               have i₂ := b4e2343
               grind)
            | exact superpose b4e2343 b4e497
            | exact resolve b4e497 b4e2343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2343
          have b4e2902 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e655 x (k X0 X0)
               have i₂ := b4e788 X0 x
               grind)
            | exact superpose b4e788 b4e655
            | (have j1 := b4e788 X0 x
               grind)
            | exact resolve b4e655 b4e788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e655 b4e788
          have b4e5118 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) := by
            first
            | (have i₁ := b4e428 (σ x) (σ y)
               have i₂ := b4e2143
               grind)
            | exact superpose b4e2143 b4e428
            | exact resolve b4e428 b4e2143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e428 b4e2143
          have b4e5127 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e5118
               have i₂ := b4e415 (σ x)
               grind)
            | exact superpose b4e415 b4e5118
            | exact resolve b4e5118 b4e415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e415 b4e5118
          have b4e7003 : (M.op (σ x) (σ y)) = (M.op x (M.op y (σ x))) := by
            first
            | (have i₁ := b4e2360 (σ x)
               have i₂ := b4e5127
               grind)
            | exact superpose b4e5127 b4e2360
            | exact resolve b4e2360 b4e5127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5127
          have b4e7023 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e497 X0 X1
               have i₂ := b4e2360 X0
               grind)
            | exact superpose b4e2360 b4e497
            | exact resolve b4e497 b4e2360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e497
          have b4e19381 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e2360 X0
               have i₂ := b4e2668 X0
               grind)
            | exact superpose b4e2668 b4e2360
            | exact resolve b4e2360 b4e2668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2360 b4e2668
          have b4e26351 : ∀ X0 X1 : G, (M.op x (M.op y (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0))) = (M.op X1 (M.op x (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e7023 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) X1
               have i₂ := b4e7023 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e7023 b4e7023
            | exact resolve b4e7023 b4e7023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26539 : ∀ X0 X1 : G, (M.op x (M.op y (M.op (M.op X1 (M.op X1 X1)) X0))) = (M.op X1 (M.op x (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26351 X0 X1
               have i₂ := b4e36 X1
               grind)
            | exact superpose b4e36 b4e26351
            | exact resolve b4e26351 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e26351
          have b4e32052 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x (M.op y (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op x y))))) := by
            intro X0
            first
            | (have i₁ := b4e19381 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op x y)))
               have i₂ := b4e731 X0 (M.op x y)
               grind)
            | exact superpose b4e731 b4e19381
            | exact resolve b4e19381 b4e731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e731 b4e19381
          have b4e32138 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x (M.op y (M.op X0 (M.op x y))))) := by
            intro X0
            first
            | (have i₁ := b4e32052 X0
               have i₂ := b4e26539 (M.op X0 (M.op x y)) X0
               grind)
            | exact superpose b4e26539 b4e32052
            | exact resolve b4e32052 b4e26539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26539 b4e32052
          have b4e32167 : ∀ X0 : G, x = (M.op X0 (M.op x (M.op y (M.op X0 (M.op x y))))) := by
            intro X0
            first
            | (have i₁ := b4e32138 X0
               have i₂ := b4e2355
               grind)
            | exact superpose b4e2355 b4e32138
            | exact resolve b4e32138 b4e2355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2355 b4e32138
          have b4e52554 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x (M.op y (k (M.op x y) (M.op x y))))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b4e32167 (k (M.op x y) (M.op x y))
               have i₂ := b4e2902 (M.op x y)
               grind)
            | exact superpose b4e2902 b4e32167
            | (have j1 := b4e2902 (M.op x y)
               grind)
            | exact resolve b4e32167 b4e2902
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2902 b4e32167
          have b4e52571 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b4e52554
               have i₂ := b4e2362 (k (M.op x y) (M.op x y))
               grind)
            | exact superpose b4e2362 b4e52554
            | exact resolve b4e52554 b4e2362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2362 b4e52554
          have b4e52585 : x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b4e52571
               have i₂ := b4e2357
               grind)
            | exact superpose b4e2357 b4e52571
            | exact resolve b4e52571 b4e2357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2357 b4e52571
          have b4e52590 : x = (k (M.op x y) (M.op x y)) := by
            first
            | (have r₁ := b4e52585
               have r₂ := b4e21
               grind)
            | exact resolve b4e52585 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52585
          have b4e53355 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (M.op X0 X0) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
            intro X0
            first
            | (have i₁ := b4e470 (M.op x y) x
               have i₂ := b4e52590
               grind)
            | exact superpose b4e52590 b4e470
            | exact resolve b4e470 b4e52590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e470 b4e52590
          have b4e53423 : (σ (M.op x y)) = (M.op x (M.op y (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b4e53355 x
               have i₂ := b4e7023 (σ x) x
               grind)
            | exact superpose b4e7023 b4e53355
            | exact resolve b4e53355 b4e7023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7023 b4e53355
          have b4e53428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b4e53423
               have i₂ := b4e7003
               grind)
            | exact superpose b4e7003 b4e53423
            | exact resolve b4e53423 b4e7003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7003 b4e53423
          have b4e53430 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b4e53428
               have r₂ := b4e20
               grind)
            | exact resolve b4e53428 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53428
          have b4e53797 : (M.op x y) = (τ (σ x)) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e53430
               grind)
            | exact superpose b4e53430 b4e14
            | exact resolve b4e14 b4e53430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53430
          have b4e53948 : x = (M.op x y) := by
            first
            | (have i₁ := b4e53797
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e53797
            | exact resolve b4e53797 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53797
          have b4e53974 : False := by grind
          exact b4e53974
        · have b5e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
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
          have b5e25 : y ≠ y ∨ y = (k y x) := by
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
          have b5e26 : y = (k y x) := by grind
          clear b5e25
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
          have b5e33 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 (M.op (M.op X0 X0) (M.op X0 X0)) X0
               have i₂ := b5e13 (M.op X0 X0) (M.op X0 X0)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e65 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e33 (M.op X0 X0)
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e33
            | exact resolve b5e33 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 X0
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) X1
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e70 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0)
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e118 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e66 (σ X0)
               have i₂ := b5e52 X0 X0
               grind)
            | exact superpose b5e52 b5e66
            | (have j1 := b5e52 X0 X0
               grind)
            | exact resolve b5e66 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e122 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e52 x y
               grind)
            | exact superpose b5e52 b5e24
            | (have j1 := b5e52 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e52 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e52 y x
               grind)
            | exact resolve b5e24 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e123 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e52 X1 X0
               grind)
            | exact superpose b5e52 b5e17
            | (have j0 := b5e17 (σ X1) (σ X0)
               have j1 := b5e52 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e52 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X0)
               have r₂ := b5e52 X0 X1
               grind)
            | exact resolve b5e17 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e129 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e123 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123
          have b5e130 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e129 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129
          have b5e131 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e122
          have b5e135 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e118 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118
          have b5e140 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e130 X0 X1
               have j1 := b5e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b5e130 X0 X1
               have r₂ := b5e16 (σ X1) (σ X0)
               grind)
            | exact resolve b5e130 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e130
          have b5e141 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e131
               have r₂ := b5e23
               grind)
            | exact resolve b5e131 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e140 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e140
            | (have j0 := b5e140 X0 X1
               grind)
            | exact resolve b5e140 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140
          have b5e148 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e141
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e141
            | exact resolve b5e141 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e141
          have b5e152 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e148
               grind)
            | exact superpose b5e148 b5e23
            | exact resolve b5e23 b5e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e309 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e69 X1 (M.op X0 X0)
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e69
            | exact resolve b5e69 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e313 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e69 (M.op (M.op X0 X0) (M.op X0 X0)) X0
               have i₂ := b5e13 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
               grind)
            | exact superpose b5e13 b5e69
            | exact resolve b5e69 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e320 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e313 X0
               have i₂ := b5e13 X0 X0
               grind)
            | exact superpose b5e13 b5e313
            | exact resolve b5e313 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313
          have b5e321 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e320 X0
               have i₂ := b5e33 (M.op X0 X0)
               grind)
            | exact superpose b5e33 b5e320
            | exact resolve b5e320 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e320
          have b5e322 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e321 X0
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e321
            | exact resolve b5e321 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e321
          have b5e323 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e322 (M.op X0 X0)
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e322
            | exact resolve b5e322 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e329 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
            intro X0
            first
            | (have i₁ := b5e323 X0
               have i₂ := b5e322 X0
               grind)
            | exact superpose b5e322 b5e323
            | exact resolve b5e323 b5e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e323
          have b5e330 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e70 (M.op X0 X0) X1
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e70
            | exact resolve b5e70 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e335 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e69 (M.op X0 (M.op X0 X0)) X0
               have i₂ := b5e70 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b5e70 b5e69
            | exact resolve b5e69 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e341 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e335 X0
               have i₂ := b5e66 X0
               grind)
            | exact superpose b5e66 b5e335
            | exact resolve b5e335 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e335
          have b5e342 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e330 X0 X1
               have i₂ := b5e322 X0
               grind)
            | exact superpose b5e322 b5e330
            | exact resolve b5e330 b5e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e330
          have b5e386 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e66 (σ X0)
               have i₂ := b5e147 X0 X0
               grind)
            | exact superpose b5e147 b5e66
            | (have j1 := b5e147 X0 X0
               grind)
            | exact resolve b5e66 b5e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e147
          have b5e455 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e70 X1 (M.op X0 (M.op X0 X0))
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e70
            | exact resolve b5e70 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e70
          have b5e469 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e455 X0 X1
               have i₂ := b5e322 X0
               grind)
            | exact superpose b5e322 b5e455
            | exact resolve b5e455 b5e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e455
          have b5e631 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b5e341 X0
               grind)
            | exact superpose b5e341 b5e13
            | exact resolve b5e13 b5e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e985 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e66 X1
               have i₂ := b5e631 X1 X0
               grind)
            | exact superpose b5e631 b5e66
            | exact resolve b5e66 b5e631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e991 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e322 X1
               have i₂ := b5e631 X1 X0
               grind)
            | exact superpose b5e631 b5e322
            | exact resolve b5e322 b5e631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e992 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e329 X1
               have i₂ := b5e631 X1 X0
               grind)
            | exact superpose b5e631 b5e329
            | exact resolve b5e329 b5e631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1095 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e985 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b5e342 X0 X0
               grind)
            | exact superpose b5e342 b5e985
            | exact resolve b5e985 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e985
          have b5e3017 : x = (M.op x (M.op (M.op y (M.op y y)) y)) := by
            first
            | (have i₁ := b5e1095 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1095
            | exact resolve b5e1095 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1095
          have b5e3042 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e3017
               have i₂ := b5e329 y
               grind)
            | exact superpose b5e329 b5e3017
            | exact resolve b5e3017 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3017
          have b5e3114 : y = (M.op (M.op x (M.op x x)) x) := by
            first
            | (have i₁ := b5e342 x y
               have i₂ := b5e3042
               grind)
            | exact superpose b5e3042 b5e342
            | exact resolve b5e342 b5e3042
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3042
          have b5e3122 : y = (M.op x x) := by
            first
            | (have i₁ := b5e3114
               have i₂ := b5e329 x
               grind)
            | exact superpose b5e329 b5e3114
            | exact resolve b5e3114 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e329 b5e3114
          have b5e3162 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e33 x
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e33
            | exact resolve b5e33 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3166 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e69 X0 x
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e69
            | exact resolve b5e69 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e3174 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b5e322 x
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e322
            | exact resolve b5e322 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e322
          have b5e3176 : x = (M.op (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b5e341 x
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e341
            | exact resolve b5e341 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e341
          have b5e3184 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e631 X0 x
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e631
            | exact resolve b5e631 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3189 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x (M.op y X0)) X0) := by
            intro X0
            first
            | (have i₁ := b5e992 x X0
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e992
            | exact resolve b5e992 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e992
          have b5e3272 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e469 X0 x
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e469
            | exact resolve b5e469 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3277 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e469 (M.op X1 (M.op X0 X0)) X1
               have i₂ := b5e342 X1 X0
               grind)
            | exact superpose b5e342 b5e469
            | exact resolve b5e469 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e342
          have b5e3334 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x (M.op y (M.op X1 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3277 X0 X1
               have i₂ := b5e3184 (M.op X1 (M.op X0 X0))
               grind)
            | exact superpose b5e3184 b5e3277
            | exact resolve b5e3277 b5e3184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3277
          have b5e3376 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op y (M.op x y)) X0)) := by
            intro X0
            first
            | (have i₁ := b5e469 X0 y
               have i₂ := b5e3162
               grind)
            | exact superpose b5e3162 b5e469
            | exact resolve b5e469 b5e3162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3398 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e3376 X0
               have i₂ := b5e3174
               grind)
            | exact superpose b5e3174 b5e3376
            | exact resolve b5e3376 b5e3174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3376
          have b5e4714 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op x y) (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e991 (M.op x y) X0
               have i₂ := b5e3176
               grind)
            | exact superpose b5e3176 b5e991
            | exact resolve b5e991 b5e3176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e991 b5e3176
          have b5e7417 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op x (M.op y X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e309 X1 X0
               have i₂ := b5e3184 X0
               grind)
            | exact superpose b5e3184 b5e309
            | exact resolve b5e309 b5e3184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e309
          have b5e7423 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e469 X0 X1
               have i₂ := b5e3184 X0
               grind)
            | exact superpose b5e3184 b5e469
            | exact resolve b5e469 b5e3184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e469
          have b5e7428 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) X0)) = (M.op x (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e631 X0 X1
               have i₂ := b5e3184 X0
               grind)
            | exact superpose b5e3184 b5e631
            | exact resolve b5e631 b5e3184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e631
          have b5e7466 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op x (M.op y X0)))) := by
            intro X0
            first
            | (have i₁ := b5e7417 X0 x
               have i₂ := b5e7423 (M.op x (M.op y X0)) x
               grind)
            | exact superpose b5e7423 b5e7417
            | exact resolve b5e7417 b5e7423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7417 b5e7423
          have b5e8500 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ X0)) (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e135 (τ X0)
               have i₂ := b5e28 X0 (τ X0)
               grind)
            | exact superpose b5e28 b5e135
            | (have j0 := b5e135 (τ X0)
               grind)
            | exact resolve b5e135 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e135
          have b5e8545 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e8500 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e8500
            | (have j0 := b5e8500 X0
               grind)
            | exact resolve b5e8500 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8500
          have b5e8581 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e8545 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e8545
            | (have j0 := b5e8545 X0
               grind)
            | exact resolve b5e8545 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8545
          have b5e10406 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e3184 X0
               have i₂ := b5e3272 X0
               grind)
            | exact superpose b5e3272 b5e3184
            | exact resolve b5e3184 b5e3272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3184 b5e3272
          have b5e12123 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op y (M.op (M.op x y) (M.op x X0)))) := by
            intro X0
            first
            | (have i₁ := b5e3166 X0
               have i₂ := b5e3398 X0
               grind)
            | exact superpose b5e3398 b5e3166
            | exact resolve b5e3166 b5e3398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3166 b5e3398
          have b5e12311 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x (M.op y (M.op x X0)))) := by
            intro X0
            first
            | (have i₁ := b5e12123 X0
               have i₂ := b5e10406 (M.op x X0)
               grind)
            | exact superpose b5e10406 b5e12123
            | exact resolve b5e12123 b5e10406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12123
          have b5e12545 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 X0)) = (M.op (M.op (M.op (M.op x x) (M.op X0 X0)) (M.op (M.op x x) (M.op X0 X0))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e4714 (M.op (M.op x x) (M.op X0 X0))
               have i₂ := b5e13 X0 x
               grind)
            | exact superpose b5e13 b5e4714
            | exact resolve b5e4714 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e12597 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 X0)) = (M.op (M.op x (M.op y (M.op x (M.op y (M.op (M.op x x) (M.op X0 X0)))))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e12545 X0
               have i₂ := b5e7466 (M.op (M.op x x) (M.op X0 X0))
               grind)
            | exact superpose b5e7466 b5e12545
            | exact resolve b5e12545 b5e7466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7466 b5e12545
          have b5e12637 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 X0)) = (M.op (M.op x (M.op y (M.op (M.op (M.op x x) (M.op x x)) X0))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e12597 X0
               have i₂ := b5e3334 X0 (M.op x x)
               grind)
            | exact superpose b5e3334 b5e12597
            | exact resolve b5e12597 b5e3334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3334 b5e12597
          have b5e12659 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 X0)) = (M.op (M.op x (M.op y (M.op (M.op x (M.op x x)) X0))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e12637 X0
               have i₂ := b5e33 x
               grind)
            | exact superpose b5e33 b5e12637
            | exact resolve b5e12637 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e12637
          have b5e12672 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op x (M.op y (M.op (M.op x y) X0))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e12659 X0
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e12659
            | exact resolve b5e12659 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12659
          have b5e12684 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e12672 X0
               have i₂ := b5e3189 (M.op (M.op x y) X0)
               grind)
            | exact superpose b5e3189 b5e12672
            | exact resolve b5e12672 b5e3189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12672
          have b5e16586 : ∀ X0 : G, (M.op (M.op (M.op y y) X0) (M.op (M.op y y) X0)) = (M.op (M.op x (M.op x (M.op y X0))) (M.op (M.op y y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e3189 (M.op (M.op y y) X0)
               have i₂ := b5e7428 X0 y
               grind)
            | exact superpose b5e7428 b5e3189
            | exact resolve b5e3189 b5e7428
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3189 b5e7428
          have b5e16596 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (M.op (M.op x (M.op x (M.op y X0))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e16586 X0
               have i₂ := b5e3162
               grind)
            | exact superpose b5e3162 b5e16586
            | exact resolve b5e16586 b5e3162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16586
          have b5e16673 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op x (M.op x (M.op y X0))) (M.op (M.op x y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e16596 X0
               have i₂ := b5e12684 X0
               grind)
            | exact superpose b5e12684 b5e16596
            | exact resolve b5e16596 b5e12684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12684 b5e16596
          have b5e22269 : ∀ X0 : G, (M.op (M.op x (M.op x (M.op y (M.op x X0)))) (M.op (M.op x y) (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4714 X0
               have i₂ := b5e12311 X0
               grind)
            | exact superpose b5e12311 b5e4714
            | exact resolve b5e4714 b5e12311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4714 b5e12311
          have b5e22374 : ∀ X0 : G, (M.op y (M.op (M.op x X0) (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e22269 X0
               have i₂ := b5e16673 (M.op x X0)
               grind)
            | exact superpose b5e16673 b5e22269
            | exact resolve b5e22269 b5e16673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16673 b5e22269
          have b5e29624 : (M.op y (M.op x x)) = (M.op x (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e22374 (M.op x (k x x))
               have i₂ := b5e8581 x
               grind)
            | exact superpose b5e8581 b5e22374
            | (have j1 := b5e8581 x
               grind)
            | exact resolve b5e22374 b5e8581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8581
          have b5e29664 : (M.op y y) = (M.op x (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e29624
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e29624
            | exact resolve b5e29624 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29624
          have b5e29696 : (M.op x y) = (M.op x (k x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e29664
               have i₂ := b5e3162
               grind)
            | exact superpose b5e3162 b5e29664
            | exact resolve b5e29664 b5e3162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3162 b5e29664
          have b5e29714 : (M.op x y) = (M.op x (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e29696
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e29696
            | exact resolve b5e29696 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29696
          have b5e30998 : (k x x) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ x = y := by
            first
            | (have i₁ := b5e22374 (k x x)
               have i₂ := b5e29714
               grind)
            | exact superpose b5e29714 b5e22374
            | exact resolve b5e22374 b5e29714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22374 b5e29714
          have b5e31014 : (k x x) = (M.op x (M.op y (M.op x y))) ∨ x = y := by
            first
            | (have i₁ := b5e30998
               have i₂ := b5e10406 (M.op x y)
               grind)
            | exact superpose b5e10406 b5e30998
            | exact resolve b5e30998 b5e10406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10406 b5e30998
          have b5e31025 : (M.op x x) = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e31014
               have i₂ := b5e3174
               grind)
            | exact superpose b5e3174 b5e31014
            | exact resolve b5e31014 b5e3174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3174 b5e31014
          have b5e31030 : y = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e31025
               have i₂ := b5e3122
               grind)
            | exact superpose b5e3122 b5e31025
            | exact resolve b5e31025 b5e3122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3122 b5e31025
          have b5e31441 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e386 x
               have i₂ := b5e31030
               grind)
            | exact superpose b5e31030 b5e386
            | exact resolve b5e386 b5e31030
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e386 b5e31030
          have b5e31498 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
            first
            | (have r₁ := b5e31441
               have r₂ := b5e152
               grind)
            | exact resolve b5e31441 b5e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31441
          have b5e31515 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e31498
               have i₂ := b5e148
               grind)
            | exact superpose b5e148 b5e31498
            | exact resolve b5e31498 b5e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e148 b5e31498
          have b5e31523 : x = y := by
            first
            | (have r₁ := b5e31515
               have r₂ := b5e23
               grind)
            | exact resolve b5e31515 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31515
          have b5e31644 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e152
               have i₂ := b5e31523
               grind)
            | exact superpose b5e31523 b5e152
            | exact resolve b5e152 b5e31523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e152 b5e31523
          have b5e31716 : False := by grind
          exact b5e31716
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e35 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b6e12 (M.op X0 X0) (M.op X0 X0)
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b6e37
        have b6e41 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have j1 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e39
             have r₂ := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e39 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e42 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e41
          | exact resolve b6e41 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e45 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e13
          | exact resolve b6e13 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e46 : y = (k y x) := by
          first
          | (have i₁ := b6e45
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e45
          | exact resolve b6e45 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
        have b6e57 : x = (M.op y x) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e52
             have r₂ := b6e21
             grind)
          | exact resolve b6e52 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e61 : x = (M.op y x) := by
          first
          | (have r₁ := b6e57
             have r₂ := b6e20
             grind)
          | exact resolve b6e57 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e64 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e46
             grind)
          | exact superpose b6e46 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e65 : y = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e64
             have r₂ := b6e20
             grind)
          | exact resolve b6e64 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e67 : y = (M.op x y) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e21
             grind)
          | exact resolve b6e65 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e74 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e61
             grind)
          | exact superpose b6e61 b6e21
          | exact resolve b6e21 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e87 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 X0
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e12
          | exact resolve b6e12 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e90 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X0 X0) X1
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e12
          | exact resolve b6e12 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e91 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0)
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e12
          | exact resolve b6e12 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e92 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e67
             grind)
          | exact superpose b6e67 b6e23
          | exact resolve b6e23 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e67
        have b6e578 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b6e90 (M.op (M.op X0 X0) (M.op X0 X0)) X0
             have i₂ := b6e12 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
             grind)
          | exact superpose b6e12 b6e90
          | exact resolve b6e90 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e585 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e578 X0
             have i₂ := b6e12 X0 X0
             grind)
          | exact superpose b6e12 b6e578
          | exact resolve b6e578 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e578
        have b6e586 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e585 X0
             have i₂ := b6e35 (M.op X0 X0)
             grind)
          | exact superpose b6e35 b6e585
          | exact resolve b6e585 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e585
        have b6e587 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e586 X0
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e586
          | exact resolve b6e586 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e586
        have b6e588 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b6e587 (M.op X0 X0)
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e587
          | exact resolve b6e587 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e594 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have i₁ := b6e588 X0
             have i₂ := b6e587 X0
             grind)
          | exact superpose b6e587 b6e588
          | exact resolve b6e588 b6e587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e588
        have b6e595 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e91 (M.op X0 X0) X1
             have i₂ := b6e35 X0
             grind)
          | exact superpose b6e35 b6e91
          | exact resolve b6e91 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e600 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b6e90 (M.op X0 (M.op X0 X0)) X0
             have i₂ := b6e91 X0 (M.op X0 (M.op X0 X0))
             grind)
          | exact superpose b6e91 b6e90
          | exact resolve b6e90 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90 b6e91
        have b6e606 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e600 X0
             have i₂ := b6e87 X0
             grind)
          | exact superpose b6e87 b6e600
          | exact resolve b6e600 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e600
        have b6e607 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e595 X0 X1
             have i₂ := b6e587 X0
             grind)
          | exact superpose b6e587 b6e595
          | exact resolve b6e595 b6e587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e587 b6e595
        have b6e695 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b6e606 X0
             grind)
          | exact superpose b6e606 b6e12
          | exact resolve b6e12 b6e606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e606
        have b6e853 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e87 X1
             have i₂ := b6e695 X1 X0
             grind)
          | exact superpose b6e695 b6e87
          | exact resolve b6e87 b6e695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87 b6e695
        have b6e937 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e853 (M.op X0 (M.op X0 X0)) X1
             have i₂ := b6e607 X0 X0
             grind)
          | exact superpose b6e607 b6e853
          | exact resolve b6e853 b6e607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e949 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e853 x (M.op X0 X0)
             have i₂ := b6e12 X0 x
             grind)
          | exact superpose b6e12 b6e853
          | exact resolve b6e853 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e853
        have b6e2431 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x))) := by
          first
          | (have i₁ := b6e937 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e937
          | exact resolve b6e937 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e937
        have b6e2464 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b6e2431
             have i₂ := b6e594 (σ x)
             grind)
          | exact superpose b6e594 b6e2431
          | exact resolve b6e2431 b6e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2431
        have b6e2870 : (σ x) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y)) := by
          first
          | (have i₁ := b6e607 (σ y) (σ x)
             have i₂ := b6e2464
             grind)
          | exact superpose b6e2464 b6e607
          | exact resolve b6e607 b6e2464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e607 b6e2464
        have b6e2879 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e2870
             have i₂ := b6e594 (σ y)
             grind)
          | exact superpose b6e594 b6e2870
          | exact resolve b6e2870 b6e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e594 b6e2870
        have b6e3018 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e51 y y
             have i₂ := b6e2879
             grind)
          | exact superpose b6e2879 b6e51
          | exact resolve b6e51 b6e2879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e2879
        have b6e3057 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e3018
        have b6e3068 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b6e3057
             have r₂ := b6e92
             grind)
          | exact resolve b6e3057 b6e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92 b6e3057
        have b6e3115 : (τ (σ x)) = (k y y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e3068
             grind)
          | exact superpose b6e3068 b6e13
          | exact resolve b6e13 b6e3068
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3068
        have b6e3170 : x = (k y y) := by
          first
          | (have i₁ := b6e3115
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3115
          | exact resolve b6e3115 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3115
        have b6e3226 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e3170
             grind)
          | exact superpose b6e3170 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e3170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3227 : y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b6e3226
        have b6e3361 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e15 y y
             have i₂ := b6e3227
             grind)
          | exact superpose b6e3227 b6e15
          | (have j0 := b6e15 y y
             grind)
          | (have r₁ := b6e15 y y
             have r₂ := b6e3227
             grind)
          | exact resolve b6e15 b6e3227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3227
        have b6e3363 : y = (k y y) ∨ x = (M.op y y) := by grind
        clear b6e3361
        have b6e3364 : x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e3363
             have i₂ := b6e3170
             grind)
          | exact superpose b6e3170 b6e3363
          | exact resolve b6e3363 b6e3170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3170 b6e3363
        have b6e3373 : x = (M.op y y) := by
          first
          | (have r₁ := b6e3364
             have r₂ := b6e74
             grind)
          | exact resolve b6e3364 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74 b6e3364
        have b6e3478 : x = (M.op x y) := by
          first
          | (have i₁ := b6e949 y
             have i₂ := b6e3373
             grind)
          | exact superpose b6e3373 b6e949
          | exact resolve b6e949 b6e3373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e949 b6e3373
        have b6e3486 : False := by grind
        exact b6e3486
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
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
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
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
          have b7e26 : (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e25
          have b7e27 : (σ y) = (σ (k y x)) := by
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
          have b7e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e32 : (k y x) = (τ (σ y)) := by
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
          have b7e33 : y = (k y x) := by
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
          have b7e36 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 (M.op (M.op X0 X0) (M.op X0 X0)) X0
               have i₂ := b7e13 (M.op X0 X0) (M.op X0 X0)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
          have b7e62 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e21
               grind)
            | exact resolve b7e59 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e66 : y = (M.op x y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e84 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e21
            | exact resolve b7e21 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e88 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 X0
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e91 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 X0) X1
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0)
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e137 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X1) (σ X0)
               have i₂ := b7e56 X1 X0
               grind)
            | exact superpose b7e56 b7e17
            | (have j0 := b7e17 (σ X1) (σ X0)
               have j1 := b7e56 X1 X0
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e56 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X0)
               have r₂ := b7e56 X0 X1
               grind)
            | exact resolve b7e17 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e143 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e137 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e137
          have b7e144 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e151 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e144 X0 X1
               have j1 := b7e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b7e144 X0 X1
               have r₂ := b7e16 (σ X1) (σ X0)
               grind)
            | exact resolve b7e144 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e144
          have b7e170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e151 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e151
            | (have j0 := b7e151 X0 X1
               grind)
            | exact resolve b7e151 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e579 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e91 (M.op (M.op X0 X0) (M.op X0 X0)) X0
               have i₂ := b7e13 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
               grind)
            | exact superpose b7e13 b7e91
            | exact resolve b7e91 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e586 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e579 X0
               have i₂ := b7e13 X0 X0
               grind)
            | exact superpose b7e13 b7e579
            | exact resolve b7e579 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e579
          have b7e587 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e586 X0
               have i₂ := b7e36 (M.op X0 X0)
               grind)
            | exact superpose b7e36 b7e586
            | exact resolve b7e586 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e586
          have b7e588 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e587 X0
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e587
            | exact resolve b7e587 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e587
          have b7e589 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e588 (M.op X0 X0)
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e588
            | exact resolve b7e588 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e595 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
            intro X0
            first
            | (have i₁ := b7e589 X0
               have i₂ := b7e588 X0
               grind)
            | exact superpose b7e588 b7e589
            | exact resolve b7e589 b7e588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e589
          have b7e596 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e92 (M.op X0 X0) X1
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e92
            | exact resolve b7e92 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e601 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e91 (M.op X0 (M.op X0 X0)) X0
               have i₂ := b7e92 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b7e92 b7e91
            | exact resolve b7e91 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91 b7e92
          have b7e607 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e601 X0
               have i₂ := b7e88 X0
               grind)
            | exact superpose b7e88 b7e601
            | exact resolve b7e601 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e601
          have b7e608 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e596 X0 X1
               have i₂ := b7e588 X0
               grind)
            | exact superpose b7e588 b7e596
            | exact resolve b7e596 b7e588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e588 b7e596
          have b7e634 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e170 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e170
            | exact resolve b7e170 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e170
          have b7e680 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e634 X0 X1
               have i₂ := b7e29 X0 X1
               grind)
            | exact superpose b7e29 b7e634
            | (have j0 := b7e634 X0 X1
               grind)
            | exact resolve b7e634 b7e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e634
          have b7e690 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e680 X0 X1
               have i₂ := b7e28 X0 X1
               grind)
            | exact superpose b7e28 b7e680
            | (have j0 := b7e680 X0 X1
               grind)
            | exact resolve b7e680 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e680
          have b7e698 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b7e607 X0
               grind)
            | exact superpose b7e607 b7e13
            | exact resolve b7e13 b7e607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e607
          have b7e856 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e88 X1
               have i₂ := b7e698 X1 X0
               grind)
            | exact superpose b7e698 b7e88
            | exact resolve b7e88 b7e698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e698
          have b7e940 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e856 (M.op X0 (M.op X0 X0)) X1
               have i₂ := b7e608 X0 X0
               grind)
            | exact superpose b7e608 b7e856
            | exact resolve b7e856 b7e608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e952 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b7e856 x (M.op X0 X0)
               have i₂ := b7e13 X0 x
               grind)
            | exact superpose b7e13 b7e856
            | exact resolve b7e856 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e856
          have b7e2436 : (σ x) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (σ y))) := by
            first
            | (have i₁ := b7e940 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e940
            | exact resolve b7e940 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e940
          have b7e2469 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b7e2436
               have i₂ := b7e595 (σ y)
               grind)
            | exact superpose b7e595 b7e2436
            | exact resolve b7e2436 b7e595
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2436
          have b7e2733 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e690 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e690
            | exact resolve b7e690 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e690
          have b7e2875 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) := by
            first
            | (have i₁ := b7e608 (σ x) (σ y)
               have i₂ := b7e2469
               grind)
            | exact superpose b7e2469 b7e608
            | exact resolve b7e608 b7e2469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e608 b7e2469
          have b7e2884 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e2875
               have i₂ := b7e595 (σ x)
               grind)
            | exact superpose b7e595 b7e2875
            | exact resolve b7e2875 b7e595
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e595 b7e2875
          have b7e3023 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e56 x x
               have i₂ := b7e2884
               grind)
            | exact superpose b7e2884 b7e56
            | exact resolve b7e56 b7e2884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e2884
          have b7e3062 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e3023
          have b7e5808 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e3062
               grind)
            | exact superpose b7e3062 b7e14
            | exact resolve b7e14 b7e3062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3062
          have b7e5869 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e5808
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e5808
            | exact resolve b7e5808 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5808
          have b7e6088 : x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2733 x x
               have i₂ := b7e5869
               grind)
            | exact superpose b7e5869 b7e2733
            | exact resolve b7e2733 b7e5869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2733 b7e5869
          have b7e6094 : y = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e6088
               have r₂ := b7e84
               grind)
            | exact resolve b7e6088 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e6088
          have b7e6349 : y = (M.op y x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e952 x
               have i₂ := b7e6094
               grind)
            | exact superpose b7e6094 b7e952
            | exact resolve b7e952 b7e6094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e952 b7e6094
          have b7e6360 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e6349
               have r₂ := b7e22
               grind)
            | exact resolve b7e6349 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6349
          have b7e6633 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e6360
               grind)
            | exact superpose b7e6360 b7e23
            | exact resolve b7e23 b7e6360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6634 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e6360
               grind)
            | exact superpose b7e6360 b7e24
            | exact resolve b7e24 b7e6360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6360
          have b7e6710 : False := by grind
          exact b7e6710
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
          have b8e44 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e113 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e24
            | (have j1 := b8e44 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e44 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e44 y x
               grind)
            | exact resolve b8e24 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e122 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e113
          have b8e132 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e122
               have r₂ := b8e23
               grind)
            | exact resolve b8e122 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e141 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e132
               grind)
            | exact superpose b8e132 b8e20
            | exact resolve b8e20 b8e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e198 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e141
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e141
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e141 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e199 : x = (M.op x y) ∨ y = (M.op y x) := by grind
          clear b8e198
          have b8e200 : y = (M.op y x) := by
            first
            | (have r₁ := b8e199
               have r₂ := b8e21
               grind)
            | exact resolve b8e199 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e199
          have b8e201 : False := by grind
          exact b8e201

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_x_pyy_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, y = (M.op X0 (M.op x (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
           have i₂ := b0e11 X0 X2 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b0e32 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e62 : ∀ X0 : G, (M.op x x) = (M.op y (M.op (M.op X0 (M.op x x)) y)) := by
        intro X0
        first
        | (have i₁ := b0e11 (M.op x x) y X0
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e200 : (M.op x x) = (M.op y (M.op y y)) := by
        first
        | (have i₁ := b0e62 y
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e62
        | exact resolve b0e62 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e203 : (M.op x x) = (M.op y x) := by
        first
        | (have i₁ := b0e200
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e200
        | exact resolve b0e200 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e200
      have b0e271 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) (M.op y x))) := by
        intro X0
        first
        | (have i₁ := b0e11 x x X0
           have i₂ := b0e203
           grind)
        | exact superpose b0e203 b0e11
        | exact resolve b0e11 b0e203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e203
      have b0e726 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 X0 X2 X2 X1
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e34
        | exact resolve b0e34 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e2235 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 x
           have i₂ := b0e726 X1 x X0
           grind)
        | exact superpose b0e726 b0e11
        | exact resolve b0e11 b0e726
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2236 : x = (M.op x (M.op y (M.op x x))) := by
        first
        | (have i₁ := b0e271 x
           have i₂ := b0e726 x x y
           grind)
        | exact superpose b0e726 b0e271
        | exact resolve b0e271 b0e726
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e271 b0e726
      have b0e2291 : x = (M.op x y) := by
        first
        | (have i₁ := b0e2236
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e2236
        | exact resolve b0e2236 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e2236
      have b0e4255 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e2235 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e2235
        | exact resolve b0e2235 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4674 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e2235 (σ x) (σ x)
           have i₂ := b0e4255 (σ x)
           grind)
        | exact superpose b0e4255 b0e2235
        | exact resolve b0e2235 b0e4255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2235 b0e4255
      have b0e5145 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e4674
           grind)
        | exact superpose b0e4674 b0e18
        | exact resolve b0e18 b0e4674
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4674
      have b0e5168 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e5145
           have i₂ := b0e2291
           grind)
        | exact superpose b0e2291 b0e5145
        | exact resolve b0e5145 b0e2291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2291 b0e5145
      have b0e5169 : False := by grind
      exact b0e5169
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : x = (k x y) := by grind
        have b1e75 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
        have b1e90 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e75
             have r₂ := b1e21
             grind)
          | exact resolve b1e75 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e91 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e90
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e90
          | exact resolve b1e90 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e92 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e91
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e91
          | exact resolve b1e91 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e91
        have b1e93 : False := by grind
        exact b1e93
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x = (k x y) := by grind
        have b2e28 : ∀ X0 : G, y = (M.op X0 (M.op x (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b2e12 y X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e71 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e257 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e45 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e258 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e257
             have r₂ := b2e22
             grind)
          | exact resolve b2e257 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e257
        have b2e259 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e258
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e258
          | exact resolve b2e258 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e258
        have b2e260 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e259
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e259
          | exact resolve b2e259 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e259
        have b2e262 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e12 (σ x) X0 (σ y)
             have i₂ := b2e260
             grind)
          | exact superpose b2e260 b2e12
          | exact resolve b2e12 b2e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e285 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b2e262 (σ y)
             have i₂ := b2e260
             grind)
          | exact superpose b2e260 b2e262
          | exact resolve b2e262 b2e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262
        have b2e508 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 X0 X2 X2 X1
             have i₂ := b2e12 X0 X2 X1
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e543 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b2e508 y y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e508
          | exact resolve b2e508 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e560 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e508 (σ x) X0 (σ y)
             have i₂ := b2e260
             grind)
          | exact superpose b2e260 b2e508
          | exact resolve b2e508 b2e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e260
        have b2e576 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 x
             have i₂ := b2e508 X1 x X0
             grind)
          | exact superpose b2e508 b2e12
          | exact resolve b2e12 b2e508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e508
        have b2e604 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e560 X0
             have i₂ := b2e285
             grind)
          | exact superpose b2e285 b2e560
          | exact resolve b2e560 b2e285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e285 b2e560
        have b2e807 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e28 X0
             have i₂ := b2e543 X0
             grind)
          | exact superpose b2e543 b2e28
          | exact resolve b2e28 b2e543
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e543
        have b2e2694 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e576 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b2e576 (M.op X0 X0) X0
             grind)
          | exact superpose b2e576 b2e576
          | exact resolve b2e576 b2e576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5180 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e2694 (σ x)
             have i₂ := b2e604 (σ x)
             grind)
          | exact superpose b2e604 b2e2694
          | exact resolve b2e2694 b2e604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e604 b2e2694
        have b2e6336 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e5180
             grind)
          | exact superpose b2e5180 b2e22
          | exact resolve b2e22 b2e5180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e6343 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b2e5180
        have b2e6400 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e6343
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e6343
          | exact resolve b2e6343 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6343
        have b2e7973 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e6400
             grind)
          | exact superpose b2e6400 b2e13
          | exact resolve b2e13 b2e6400
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6400
        have b2e7991 : x = (k x x) := by
          first
          | (have i₁ := b2e7973
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e7973
          | exact resolve b2e7973 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7973
        have b2e8128 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e71 x x
             have i₂ := b2e7991
             grind)
          | exact superpose b2e7991 b2e71
          | (have j0 := b2e71 x x
             grind)
          | exact resolve b2e71 b2e7991
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71 b2e7991
        have b2e8129 : x = (M.op x x) := by grind
        clear b2e8128
        have b2e8264 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e576 X0 x
             have i₂ := b2e8129
             grind)
          | exact superpose b2e8129 b2e576
          | exact resolve b2e576 b2e8129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e576 b2e8129
        have b2e8291 : x = y := by
          first
          | (have i₁ := b2e8264 x
             have i₂ := b2e807 x
             grind)
          | exact superpose b2e807 b2e8264
          | exact resolve b2e8264 b2e807
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e807 b2e8264
        have b2e8408 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e6336
             have i₂ := b2e8291
             grind)
          | exact superpose b2e8291 b2e6336
          | exact resolve b2e6336 b2e8291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6336 b2e8291
        have b2e8412 : False := by grind
        exact b2e8412
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e27 : (σ x) = (σ (k x y)) := by
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
        have b3e32 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e13
          | exact resolve b3e13 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e33 : x = (k x y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e32
          | exact resolve b3e32 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e74 : (M.op y y) = (k x y) ∨ x = (M.op y y) := by grind
        have b3e86 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e74
             have r₂ := b3e20
             grind)
          | exact resolve b3e74 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e88 : x = (M.op y y) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e86
          | exact resolve b3e86 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e86
        have b3e91 : False := by grind
        exact b3e91
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
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
          have b4e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b4e36 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e68 : ∀ X0 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op y y)) x)) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op y y) x X0
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e13
            | exact resolve b4e13 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
          have b4e74 : (M.op y y) = (k x y) ∨ x = (M.op y y) := by grind
          have b4e86 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b4e74
               have r₂ := b4e21
               grind)
            | exact resolve b4e74 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e87 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e73
               have r₂ := b4e23
               grind)
            | exact resolve b4e73 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e88 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e87
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e87
            | exact resolve b4e87 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e89 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e88
               have i₂ := b4e86
               grind)
            | exact superpose b4e86 b4e88
            | exact resolve b4e88 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86 b4e88
          have b4e279 : (M.op y y) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e68 x
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e68
            | exact resolve b4e68 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e68
          have b4e282 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e279
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e279
            | exact resolve b4e279 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e279
          have b4e684 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 X0 X2 X2 X1
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e1303 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 x
               have i₂ := b4e684 X1 x X0
               grind)
            | exact superpose b4e684 b4e13
            | exact resolve b4e13 b4e684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e684
          have b4e3847 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e1303 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1303
            | exact resolve b4e1303 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3909 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
               have i₂ := b4e1303 (M.op X1 (M.op X0 X0)) X0
               grind)
            | exact superpose b4e1303 b4e13
            | exact resolve b4e13 b4e1303
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1303
          have b4e11227 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e3909 (σ y) (σ y)
               have i₂ := b4e3847 (σ y)
               grind)
            | exact superpose b4e3847 b4e3909
            | exact resolve b4e3909 b4e3847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3847 b4e3909
          have b4e11345 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e11227
               have i₂ := b4e89
               grind)
            | exact superpose b4e89 b4e11227
            | exact resolve b4e11227 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89 b4e11227
          have b4e11379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e11345
               have i₂ := b4e282
               grind)
            | exact superpose b4e282 b4e11345
            | exact resolve b4e11345 b4e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e282 b4e11345
          have b4e11401 : False := by grind
          exact b4e11401
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : y = (k y x) := by grind
          have b5e34 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e34 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e34
            | exact resolve b5e34 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e52 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ x)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op y y)) x)) := by
            intro X0
            first
            | (have i₁ := b5e13 (M.op y y) x X0
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e66 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e246 : (M.op y y) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e62 x
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e62
            | exact resolve b5e62 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e62
          have b5e255 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e246
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e246
            | exact resolve b5e246 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e246
          have b5e270 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e52 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e271 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e270
               have r₂ := b5e23
               grind)
            | exact resolve b5e270 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e270
          have b5e272 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e271
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e271
            | exact resolve b5e271 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e271
          have b5e273 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e272
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e272
            | exact resolve b5e272 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e272
          have b5e285 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e20
            | exact resolve b5e20 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e287 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e13 (σ y) X0 (σ x)
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e13
            | exact resolve b5e13 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e345 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e77 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e346 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e345 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e345
          have b5e498 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 X0 X2 X2 X1
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e1623 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b5e287 (σ x)
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e287
            | exact resolve b5e287 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e287
          have b5e2079 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e498 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e498
            | exact resolve b5e498 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2115 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e498 (σ y) X0 (σ x)
               have i₂ := b5e273
               grind)
            | exact superpose b5e273 b5e498
            | exact resolve b5e498 b5e273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e273
          have b5e2150 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 x
               have i₂ := b5e498 X1 x X0
               grind)
            | exact superpose b5e498 b5e13
            | exact resolve b5e13 b5e498
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e498
          have b5e2222 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e2115 X0
               have i₂ := b5e1623
               grind)
            | exact superpose b5e1623 b5e2115
            | exact resolve b5e2115 b5e1623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1623 b5e2115
          have b5e3428 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e34 X0
               have i₂ := b5e2079 X0
               grind)
            | exact superpose b5e2079 b5e34
            | exact resolve b5e34 b5e2079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e2079
          have b5e4868 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b5e2150 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b5e2150 (M.op X0 X0) X0
               grind)
            | exact superpose b5e2150 b5e2150
            | exact resolve b5e2150 b5e2150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2150
          have b5e8600 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e4868 (σ y)
               have i₂ := b5e2222 (σ y)
               grind)
            | exact superpose b5e2222 b5e4868
            | exact resolve b5e4868 b5e2222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2222 b5e4868
          have b5e8773 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b5e8600
          have b5e8835 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e8773
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e8773
            | exact resolve b5e8773 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8773
          have b5e9056 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e8835
               have i₂ := b5e346 y
               grind)
            | exact superpose b5e346 b5e8835
            | (have j1 := b5e346 y
               grind)
            | exact resolve b5e8835 b5e346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e346 b5e8835
          have b5e9092 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e9056
               have i₂ := b5e255
               grind)
            | exact superpose b5e255 b5e9056
            | exact resolve b5e9056 b5e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e255 b5e9056
          have b5e9102 : y = (M.op y y) := by
            first
            | (have r₁ := b5e9092
               have r₂ := b5e285
               grind)
            | exact resolve b5e9092 b5e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e285 b5e9092
          have b5e9603 : x = (M.op y y) := by
            first
            | (have i₁ := b5e3428 y
               have i₂ := b5e9102
               grind)
            | exact superpose b5e9102 b5e3428
            | exact resolve b5e3428 b5e9102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3428 b5e9102
          have b5e9668 : False := by grind
          exact b5e9668
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
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
        have b6e27 : (k x y) = (τ (σ x)) := by
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
        have b6e28 : x = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e73 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e28
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e28 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e76 : x = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e20
             grind)
          | exact resolve b6e73 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e79 : x = (M.op y x) := by
          first
          | (have r₁ := b6e76
             have r₂ := b6e21
             grind)
          | exact resolve b6e76 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e81 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b6e12 x y X0
             have i₂ := b6e79
             grind)
          | exact superpose b6e79 b6e12
          | exact resolve b6e12 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e84 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e86 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        have b6e96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e98 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e86
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e86
          | exact resolve b6e86 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e110 : x = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b6e81 y
             have i₂ := b6e79
             grind)
          | exact superpose b6e79 b6e81
          | exact resolve b6e81 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e81
        have b6e118 : ∀ X0 : G, (M.op x x) = (M.op y (M.op (M.op X0 (M.op x x)) x)) := by
          intro X0
          first
          | (have i₁ := b6e12 (M.op x x) y X0
             have i₂ := b6e110
             grind)
          | exact superpose b6e110 b6e12
          | exact resolve b6e12 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e345 : (M.op x x) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b6e118 y
             have i₂ := b6e110
             grind)
          | exact superpose b6e110 b6e118
          | exact resolve b6e118 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e118
        have b6e348 : x = (M.op x x) := by
          first
          | (have i₁ := b6e345
             have i₂ := b6e110
             grind)
          | exact superpose b6e110 b6e345
          | exact resolve b6e345 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110 b6e345
        have b6e383 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e348
             grind)
          | exact superpose b6e348 b6e21
          | exact resolve b6e21 b6e348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e386 : x = (k x x) := by grind
        clear b6e348
        have b6e461 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e96 y x
             grind)
          | exact superpose b6e96 b6e28
          | (have j1 := b6e96 y x
             grind)
          | exact resolve b6e28 b6e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e96
        have b6e468 : x = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
        clear b6e461
        have b6e482 : (M.op x y) = (k y x) := by
          first
          | (have r₁ := b6e468
             have r₂ := b6e20
             grind)
          | exact resolve b6e468 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e468
        have b6e664 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e40 X0 X2 X2 X1
             have i₂ := b6e12 X0 X2 X1
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e1458 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 x
             have i₂ := b6e664 X1 x X0
             grind)
          | exact superpose b6e664 b6e12
          | exact resolve b6e12 b6e664
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e664
        have b6e1831 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e1458 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1458
          | exact resolve b6e1458 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2703 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e1458 (σ x) (σ x)
             have i₂ := b6e1831 (σ x)
             grind)
          | exact superpose b6e1831 b6e1458
          | exact resolve b6e1458 b6e1831
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1458 b6e1831
        have b6e2798 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e2703
             grind)
          | exact superpose b6e2703 b6e19
          | exact resolve b6e19 b6e2703
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2703
        have b6e2840 : (σ (k y x)) = (σ (k x x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e71 x x
             have i₂ := b6e98
             grind)
          | exact superpose b6e98 b6e71
          | (have j0 := b6e71 x y
             grind)
          | exact resolve b6e71 b6e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2926 : (σ (k y x)) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e98
             have i₂ := b6e71 x x
             grind)
          | exact superpose b6e71 b6e98
          | (have j1 := b6e71 x x
             grind)
          | exact resolve b6e98 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71 b6e98
        have b6e3100 : (σ (k y x)) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b6e2926
        have b6e3120 : (σ (k y x)) = (σ (k x x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b6e2840
        have b6e3154 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3100
             have i₂ := b6e386
             grind)
          | exact superpose b6e386 b6e3100
          | exact resolve b6e3100 b6e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3100
        have b6e3180 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3120
             have i₂ := b6e386
             grind)
          | exact superpose b6e386 b6e3120
          | exact resolve b6e3120 b6e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3120
        have b6e3181 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        clear b6e3180
        have b6e3201 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3154
             have i₂ := b6e482
             grind)
          | exact superpose b6e482 b6e3154
          | exact resolve b6e3154 b6e482
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3154
        have b6e3210 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3181
             have i₂ := b6e482
             grind)
          | exact superpose b6e482 b6e3181
          | exact resolve b6e3181 b6e482
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e482 b6e3181
        have b6e3220 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b6e3201
             have r₂ := b6e2798
             grind)
          | exact resolve b6e3201 b6e2798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3201
        have b6e3221 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b6e3210
             have r₂ := b6e2798
             grind)
          | exact resolve b6e3210 b6e2798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2798 b6e3210
        have b6e3222 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3220
             have i₂ := b6e386
             grind)
          | exact superpose b6e386 b6e3220
          | exact resolve b6e3220 b6e386
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e386 b6e3220
        have b6e3223 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3222
             have i₂ := b6e3221
             grind)
          | exact superpose b6e3221 b6e3222
          | exact resolve b6e3222 b6e3221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3221 b6e3222
        have b6e3224 : (σ x) = (σ y) := by grind
        clear b6e3223
        have b6e3232 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e3224
             grind)
          | exact superpose b6e3224 b6e13
          | exact resolve b6e13 b6e3224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3224
        have b6e3249 : x = y := by
          first
          | (have i₁ := b6e3232
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3232
          | exact resolve b6e3232 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3232
        have b6e3255 : False := by grind
        exact b6e3255
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ y) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e27
            | exact resolve b7e27 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e28
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e34 : y = (k y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e67 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : y = (M.op x y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e73 : y = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e75 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b7e13 y x X0
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e13
            | exact resolve b7e13 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e80 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
          have b7e90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e92 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e23
               grind)
            | exact resolve b7e80 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e93 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e92
            | exact resolve b7e92 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e110 : y = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b7e75 x
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e75
            | exact resolve b7e75 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e477 : y = (M.op x x) ∨ (k x y) = (M.op y x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e90 x y
               grind)
            | exact superpose b7e90 b7e34
            | (have j1 := b7e90 x y
               grind)
            | exact resolve b7e34 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e90
          have b7e484 : y = (M.op x x) ∨ (k x y) = (M.op y x) := by grind
          clear b7e477
          have b7e500 : (k x y) = (M.op y x) := by
            first
            | (have r₁ := b7e484
               have r₂ := b7e22
               grind)
            | exact resolve b7e484 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e484
          have b7e700 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e38 X0 X2 X2 X1
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e38
            | exact resolve b7e38 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1074 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op x (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e700 y X0 x
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e700
            | exact resolve b7e700 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1092 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 x
               have i₂ := b7e700 X1 x X0
               grind)
            | exact superpose b7e700 b7e13
            | exact resolve b7e13 b7e700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1133 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b7e1074 X0
               have i₂ := b7e110
               grind)
            | exact superpose b7e110 b7e1074
            | exact resolve b7e1074 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110 b7e1074
          have b7e1357 : y = (M.op y y) := by
            first
            | (have i₁ := b7e1133 x
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e1133
            | exact resolve b7e1133 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e1133
          have b7e1590 : y = (k y y) := by grind
          have b7e1604 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e700 y y x
               have i₂ := b7e1357
               grind)
            | exact superpose b7e1357 b7e700
            | exact resolve b7e700 b7e1357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2501 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e1092 X0 y
               have i₂ := b7e1357
               grind)
            | exact superpose b7e1357 b7e1092
            | exact resolve b7e1092 b7e1357
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1357
          have b7e2529 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e38 X1 X1 X0 X0
               have i₂ := b7e1092 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e1092 b7e38
            | exact resolve b7e38 b7e1092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e1092
          have b7e2561 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e2529 X0 X1
               have i₂ := b7e700 X1 X0 X0
               grind)
            | exact superpose b7e700 b7e2529
            | exact resolve b7e2529 b7e700
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2529
          have b7e2699 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65 y y
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e65
            | exact resolve b7e65 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e93
          have b7e2988 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
          clear b7e2699
          have b7e3060 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e2988
               have i₂ := b7e1590
               grind)
            | exact superpose b7e1590 b7e2988
            | exact resolve b7e2988 b7e1590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1590 b7e2988
          have b7e3061 : (σ y) = (σ (k x y)) := by grind
          clear b7e3060
          have b7e3107 : (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b7e3061
               have i₂ := b7e500
               grind)
            | exact superpose b7e500 b7e3061
            | exact resolve b7e3061 b7e500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e500 b7e3061
          have b7e3199 : (τ (σ y)) = (M.op y x) := by
            first
            | (have i₁ := b7e14 (M.op y x)
               have i₂ := b7e3107
               grind)
            | exact superpose b7e3107 b7e14
            | exact resolve b7e14 b7e3107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3107
          have b7e3216 : y = (M.op y x) := by
            first
            | (have i₁ := b7e3199
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e3199
            | exact resolve b7e3199 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3199
          have b7e3470 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) y)) := by
            intro X0
            first
            | (have i₁ := b7e13 x y X0
               have i₂ := b7e3216
               grind)
            | exact superpose b7e3216 b7e13
            | exact resolve b7e13 b7e3216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3483 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op y (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b7e700 x X0 y
               have i₂ := b7e3216
               grind)
            | exact superpose b7e3216 b7e700
            | exact resolve b7e700 b7e3216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e700
          have b7e3485 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op x (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b7e3483 X0
               have i₂ := b7e2561 y x
               grind)
            | exact superpose b7e2561 b7e3483
            | exact resolve b7e3483 b7e2561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2561 b7e3483
          have b7e3488 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b7e3470 X0
               have i₂ := b7e1604 (M.op X0 x)
               grind)
            | exact superpose b7e1604 b7e3470
            | exact resolve b7e3470 b7e1604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1604 b7e3470
          have b7e3491 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b7e3485 X0
               have i₂ := b7e3216
               grind)
            | exact superpose b7e3216 b7e3485
            | exact resolve b7e3485 b7e3216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3216 b7e3485
          have b7e3492 : x = (M.op x y) := by
            first
            | (have i₁ := b7e3491 x
               have i₂ := b7e3488 x
               grind)
            | exact superpose b7e3488 b7e3491
            | exact resolve b7e3491 b7e3488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3488 b7e3491
          have b7e4072 : y = (M.op x x) := by
            first
            | (have i₁ := b7e2501 x
               have i₂ := b7e3492
               grind)
            | exact superpose b7e3492 b7e2501
            | exact resolve b7e2501 b7e3492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2501 b7e3492
          have b7e4095 : False := by grind
          exact b7e4095
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e45 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
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
          have b8e261 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e45 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45
          have b8e262 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e261
               have r₂ := b8e23
               grind)
            | exact resolve b8e261 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e261
          have b8e263 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e262
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e262
            | exact resolve b8e262 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e262
          have b8e264 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e263
               grind)
            | exact superpose b8e263 b8e20
            | exact resolve b8e20 b8e263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e263
          have b8e273 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e264
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e264
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e264 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e264
          have b8e274 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e273
          have b8e277 : x = (M.op y y) := by
            first
            | (have r₁ := b8e274
               have r₂ := b8e22
               grind)
            | exact resolve b8e274 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e274
          have b8e281 : False := by grind
          exact b8e281

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation947 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
          have b5e40 : ∀ X0 : G, y = (M.op X0 (M.op x (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e40 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40
            | exact resolve b5e40 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e108 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41 X0 X2 X2 X1
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e41
            | exact resolve b5e41 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e300 : ∀ X0 : G, (M.op (M.op X0 (M.op x x)) y) = (M.op x (M.op (M.op x x) (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e108 (M.op x x) X0 x
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e108
            | exact resolve b5e108 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e305 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 x
               have i₂ := b5e108 X1 x X0
               grind)
            | exact superpose b5e108 b5e13
            | exact resolve b5e13 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e321 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x x)) y) := by
            intro X0
            first
            | (have i₁ := b5e300 X0
               have i₂ := b5e13 x x x
               grind)
            | exact superpose b5e13 b5e300
            | exact resolve b5e300 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e300
          have b5e372 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e305 X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e305
            | exact resolve b5e305 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e456 : x = (M.op y y) := by
            first
            | (have i₁ := b5e321 x
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e321
            | exact resolve b5e321 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e321
          have b5e2788 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e372 y X0
               have i₂ := b5e456
               grind)
            | exact superpose b5e456 b5e372
            | exact resolve b5e372 b5e456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e372 b5e456
          have b5e3043 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e305 (σ x) (σ x)
               have i₂ := b5e2788 (σ x)
               grind)
            | exact superpose b5e2788 b5e305
            | exact resolve b5e305 b5e2788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e305 b5e2788
          have b5e3071 : False := by grind
          exact b5e3071
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e47 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (σ y) = (σ (k x y)) := by
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
          have b7e51 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e14
            | exact resolve b7e14 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : y = (k x y) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e51
            | exact resolve b7e51 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e63 : y = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : y = (M.op y x) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e81 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 y
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e13
            | exact resolve b7e13 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e93 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e33 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e98 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e93
            | exact resolve b7e93 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e93
          have b7e133 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 X0 X2 X2 X1
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e380 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op (M.op y (M.op X0 x)) (M.op y (M.op X0 x)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e133 (M.op y (M.op X0 x)) X0 X1
               have i₂ := b7e81 X0
               grind)
            | exact superpose b7e81 b7e133
            | exact resolve b7e133 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e416 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 x
               have i₂ := b7e133 X1 x X0
               grind)
            | exact superpose b7e133 b7e13
            | exact resolve b7e13 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e457 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op y (M.op (M.op X0 x) (M.op X0 x)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e380 X0 X1
               have i₂ := b7e133 (M.op X0 x) y y
               grind)
            | exact superpose b7e133 b7e380
            | exact resolve b7e380 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e380
          have b7e482 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op y (M.op X0 (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e457 X0 X1
               have i₂ := b7e133 x X0 X0
               grind)
            | exact superpose b7e133 b7e457
            | exact resolve b7e457 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e457
          have b7e510 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e416 X2 (M.op X0 X1)
               have i₂ := b7e133 X1 X0 X0
               grind)
            | exact superpose b7e133 b7e416
            | exact resolve b7e416 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e513 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b7e416 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b7e416 (M.op X0 X0) X0
               grind)
            | exact superpose b7e416 b7e416
            | exact resolve b7e416 b7e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e518 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X1 X1 X0 X0
               have i₂ := b7e416 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e416 b7e34
            | exact resolve b7e34 b7e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e526 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) = (M.op X2 (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e133 (M.op X2 (M.op X0 X0)) X1 X2
               have i₂ := b7e416 X2 X0
               grind)
            | exact superpose b7e416 b7e133
            | exact resolve b7e133 b7e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e527 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e133 (M.op X1 (M.op X0 X0)) X1 X2
               have i₂ := b7e416 X1 X0
               grind)
            | exact superpose b7e416 b7e133
            | exact resolve b7e133 b7e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e531 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
               have i₂ := b7e416 (M.op X1 (M.op X0 X0)) X0
               grind)
            | exact superpose b7e416 b7e13
            | exact resolve b7e13 b7e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e416
          have b7e534 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e527 X0 X1 X2
               have i₂ := b7e133 (M.op X0 X0) X1 X1
               grind)
            | exact superpose b7e133 b7e527
            | exact resolve b7e527 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e527
          have b7e535 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e526 X0 X1 X2
               have i₂ := b7e13 (M.op X0 X0) X2 X2
               grind)
            | exact superpose b7e13 b7e526
            | exact resolve b7e526 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e526
          have b7e537 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e518 X0 X1
               have i₂ := b7e133 X1 X0 X0
               grind)
            | exact superpose b7e133 b7e518
            | exact resolve b7e518 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e518
          have b7e540 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e534 X0 X1 X2
               have i₂ := b7e133 X0 X0 X0
               grind)
            | exact superpose b7e133 b7e534
            | exact resolve b7e534 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e534
          have b7e623 : x = (M.op (M.op x x) (M.op y (M.op x x))) := by
            first
            | (have i₁ := b7e81 (M.op x x)
               have i₂ := b7e513 x
               grind)
            | exact superpose b7e513 b7e81
            | exact resolve b7e81 b7e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e626 : x = (M.op y (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b7e623
               have i₂ := b7e537 y (M.op x x)
               grind)
            | exact superpose b7e537 b7e623
            | exact resolve b7e623 b7e537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e623
          have b7e634 : x = (M.op y (M.op x (M.op (M.op x x) x))) := by
            first
            | (have i₁ := b7e626
               have i₂ := b7e537 (M.op x x) x
               grind)
            | exact superpose b7e537 b7e626
            | exact resolve b7e626 b7e537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e537 b7e626
          have b7e641 : x = (M.op y (M.op x (M.op x x))) := by
            first
            | (have i₁ := b7e634
               have i₂ := b7e513 x
               grind)
            | exact superpose b7e513 b7e634
            | exact resolve b7e634 b7e513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e513 b7e634
          have b7e698 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x x))) x) = (M.op y (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b7e133 (M.op x (M.op x x)) X0 y
               have i₂ := b7e641
               grind)
            | exact superpose b7e641 b7e133
            | exact resolve b7e133 b7e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133 b7e641
          have b7e701 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x x))) x) = (M.op x (M.op y (M.op (M.op x (M.op x x)) (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b7e698 X0
               have i₂ := b7e540 x (M.op x (M.op x x)) y
               grind)
            | exact superpose b7e540 b7e698
            | exact resolve b7e698 b7e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e540 b7e698
          have b7e706 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x x))) x) = (M.op x (M.op x (M.op y (M.op (M.op x (M.op x x)) x)))) := by
            intro X0
            first
            | (have i₁ := b7e701 X0
               have i₂ := b7e482 (M.op x (M.op x x)) x
               grind)
            | exact superpose b7e482 b7e701
            | exact resolve b7e701 b7e482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e482 b7e701
          have b7e708 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x x))) x) = (M.op x (M.op x (M.op y (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b7e706 X0
               have i₂ := b7e531 x x
               grind)
            | exact superpose b7e531 b7e706
            | exact resolve b7e706 b7e531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e531 b7e706
          have b7e710 : ∀ X0 : G, (M.op y x) = (M.op (M.op X0 (M.op x (M.op x x))) x) := by
            intro X0
            first
            | (have i₁ := b7e708 X0
               have i₂ := b7e510 y x x
               grind)
            | exact superpose b7e510 b7e708
            | exact resolve b7e708 b7e510
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e510 b7e708
          have b7e712 : (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b7e710 x
               have i₂ := b7e535 x x x
               grind)
            | exact superpose b7e535 b7e710
            | exact resolve b7e710 b7e535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e535 b7e710
          have b7e714 : y = (M.op x x) := by
            first
            | (have i₁ := b7e712
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e712
            | exact resolve b7e712 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e712
          have b7e752 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e714
               grind)
            | exact superpose b7e714 b7e98
            | exact resolve b7e98 b7e714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98 b7e714
          have b7e768 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e752
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e752
            | exact resolve b7e752 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e752
          have b7e770 : False := by grind
          exact b7e770
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
               have i₂ := b8e13 X0 X1 X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e68 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X2 X2 X1
               have i₂ := b8e13 X0 X2 X1
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e95 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (M.op X2 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 (σ X0) (σ X0) X2 x
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e33
            | exact resolve b8e33 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
               have i₂ := b8e33 X1 (M.op X2 X1) X3 X0
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e106 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e105 X1 x X2 X3
               have i₂ := b8e68 x X1 (M.op X2 x)
               grind)
            | exact superpose b8e68 b8e105
            | exact resolve b8e105 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e119 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
            intro X1 X3
            first
            | (have i₁ := b8e106 x X1 X3
               have i₂ := b8e68 x X1 x
               grind)
            | exact superpose b8e68 b8e106
            | exact resolve b8e106 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e166 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 (σ X0) (σ X1)
               have i₂ := b8e55 X1 X0
               grind)
            | exact superpose b8e55 b8e17
            | (have j0 := b8e17 (σ X0) (σ X1)
               have j1 := b8e55 X1 X0
               grind)
            | (have r₁ := b8e17 (σ X1) (σ X0)
               have r₂ := b8e55 X0 X1
               grind)
            | exact resolve b8e17 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e172 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e166 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166
          have b8e173 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e172 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e172
          have b8e177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e173 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e173
            | (have j0 := b8e173 X0 X1
               grind)
            | exact resolve b8e173 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e240 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e68 (σ X0) X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e68
            | exact resolve b8e68 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e247 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0 x
               have i₂ := b8e68 X1 x X0
               grind)
            | exact superpose b8e68 b8e13
            | exact resolve b8e13 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e295 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e247 X2 (M.op X0 X1)
               have i₂ := b8e68 X1 X0 X0
               grind)
            | exact superpose b8e68 b8e247
            | exact resolve b8e247 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e296 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b8e247 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b8e247 (M.op X0 X0) X0
               grind)
            | exact superpose b8e247 b8e247
            | exact resolve b8e247 b8e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e297 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e247 (M.op X1 X0) X0
               have i₂ := b8e68 X0 X1 X0
               grind)
            | exact superpose b8e68 b8e247
            | exact resolve b8e247 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e300 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X1 X1 X0 X0
               have i₂ := b8e247 X1 (M.op X0 X1)
               grind)
            | exact superpose b8e247 b8e32
            | exact resolve b8e32 b8e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e308 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) = (M.op X2 (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e68 (M.op X2 (M.op X0 X0)) X1 X2
               have i₂ := b8e247 X2 X0
               grind)
            | exact superpose b8e247 b8e68
            | exact resolve b8e68 b8e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e313 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
               have i₂ := b8e247 (M.op X1 (M.op X0 X0)) X0
               grind)
            | exact superpose b8e247 b8e13
            | exact resolve b8e13 b8e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e317 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e308 X0 X1 X2
               have i₂ := b8e13 (M.op X0 X0) X2 X2
               grind)
            | exact superpose b8e13 b8e308
            | exact resolve b8e308 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e308
          have b8e319 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e300 X0 X1
               have i₂ := b8e68 X1 X0 X0
               grind)
            | exact superpose b8e68 b8e300
            | exact resolve b8e300 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e300
          have b8e382 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e68 X0 X1 (M.op X0 X0)
               have i₂ := b8e296 X0
               grind)
            | exact superpose b8e296 b8e68
            | exact resolve b8e68 b8e296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e392 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e382 X0 X1
               have i₂ := b8e319 (M.op X1 X0) X0
               grind)
            | exact superpose b8e319 b8e382
            | exact resolve b8e382 b8e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e382
          have b8e398 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e392 X0 X1
               have i₂ := b8e319 (M.op X0 X0) X0
               grind)
            | exact superpose b8e319 b8e392
            | exact resolve b8e392 b8e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e392
          have b8e403 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e398 X0 X1
               have i₂ := b8e296 X0
               grind)
            | exact superpose b8e296 b8e398
            | exact resolve b8e398 b8e296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e296 b8e398
          have b8e600 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X0 X0)))) = (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
            intro X0 X2
            first
            | (have i₁ := b8e68 (M.op X0 (M.op X0 X0)) (M.op x X0) X2
               have i₂ := b8e297 X0 x
               grind)
            | exact superpose b8e297 b8e68
            | exact resolve b8e68 b8e297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e297
          have b8e601 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X0 X0)))) = (M.op X2 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
            intro X0 X2
            first
            | (have i₁ := b8e600 X0 X2
               have i₂ := b8e68 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b8e68 b8e600
            | exact resolve b8e600 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e600
          have b8e619 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X0 (M.op X2 (M.op X0 (M.op X0 X0)))) := by
            intro X0 X2
            first
            | (have i₁ := b8e601 X0 X2
               have i₂ := b8e13 X0 X0 X0
               grind)
            | exact superpose b8e13 b8e601
            | exact resolve b8e601 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e601
          have b8e823 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ X0) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e319 X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e319
            | exact resolve b8e319 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e843 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e247 X1 X0
               have i₂ := b8e319 X1 X0
               grind)
            | (have i₁ := b8e247 X1 X1
               have i₂ := b8e319 X1 X1
               grind)
            | exact superpose b8e319 b8e247
            | exact resolve b8e247 b8e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e970 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e119 (M.op X1 X1) x
               have i₂ := b8e247 (M.op X1 X1) X1
               grind)
            | exact superpose b8e247 b8e119
            | exact resolve b8e119 b8e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e1025 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e970 (M.op X1 (M.op X0 X0)) X1
               have i₂ := b8e247 X1 X0
               grind)
            | exact superpose b8e247 b8e970
            | exact resolve b8e970 b8e247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1076 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1025 X0 X1
               have i₂ := b8e68 (M.op X0 X0) X1 X1
               grind)
            | exact superpose b8e68 b8e1025
            | exact resolve b8e1025 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1025
          have b8e1092 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1076 X0 X1
               have i₂ := b8e319 (M.op X0 X0) X0
               grind)
            | exact superpose b8e319 b8e1076
            | exact resolve b8e1076 b8e319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319 b8e1076
          have b8e1102 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1092 X0 X1
               have i₂ := b8e403 X0 X0
               grind)
            | exact superpose b8e403 b8e1092
            | exact resolve b8e1092 b8e403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1092
          have b8e1215 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e970 (M.op X0 (M.op X1 X0)) X1
               have i₂ := b8e843 X0 X1
               grind)
            | exact superpose b8e843 b8e970
            | exact resolve b8e970 b8e843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e970
          have b8e1217 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1215 X0 X1
               have i₂ := b8e68 (M.op X1 X0) X0 X0
               grind)
            | exact superpose b8e68 b8e1215
            | exact resolve b8e1215 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1215
          have b8e1236 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1217 X0 X1
               have i₂ := b8e68 X0 X1 X1
               grind)
            | exact superpose b8e68 b8e1217
            | exact resolve b8e1217 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68 b8e1217
          have b8e1922 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e177 y x
               grind)
            | exact superpose b8e177 b8e20
            | (have j1 := b8e177 x y
               grind)
            | exact resolve b8e20 b8e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177
          have b8e1958 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b8e1922
               have r₂ := b8e23
               grind)
            | exact resolve b8e1922 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1922
          have b8e3013 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e295 X1 (M.op X1 X0) X2
               have i₂ := b8e13 X0 X1 X1
               grind)
            | exact superpose b8e13 b8e295
            | exact resolve b8e295 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3572 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e295 X1 X1 X2
               have i₂ := b8e3013 X1 X1 X0
               grind)
            | (have i₁ := b8e295 X1 X1 X2
               have i₂ := b8e3013 X1 X0 X1
               grind)
            | exact superpose b8e3013 b8e295
            | exact resolve b8e295 b8e3013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e295
          have b8e3574 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e247 X1 X1
               have i₂ := b8e3013 X1 X1 X0
               grind)
            | (have i₁ := b8e247 X1 X1
               have i₂ := b8e3013 X1 X0 X1
               grind)
            | exact superpose b8e3013 b8e247
            | exact resolve b8e247 b8e3013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e247
          have b8e9120 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e619 X0 (M.op X1 (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))))
               have i₂ := b8e317 (M.op X0 (M.op X0 X0)) X1 X2
               grind)
            | exact superpose b8e317 b8e619
            | exact resolve b8e619 b8e317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e317 b8e619
          have b8e9212 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e9120 X0 X1 X2
               have i₂ := b8e1102 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b8e1102 b8e9120
            | exact resolve b8e9120 b8e1102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1102 b8e9120
          have b8e9242 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X0))))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e9212 X0 X1 X2
               have i₂ := b8e1236 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b8e1236 b8e9212
            | exact resolve b8e9212 b8e1236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1236 b8e9212
          have b8e9261 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 (M.op X0 (M.op X0 X0))))) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e9242 X0 X1 X2
               have i₂ := b8e313 X0 X0
               grind)
            | exact superpose b8e313 b8e9242
            | exact resolve b8e9242 b8e313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e313 b8e9242
          have b8e9274 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e9261 X0 X1 X2
               have i₂ := b8e843 X0 X0
               grind)
            | exact superpose b8e843 b8e9261
            | exact resolve b8e9261 b8e843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e843 b8e9261
          have b8e14787 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3572 X1 X2 X1
               have i₂ := b8e3013 (M.op X1 X2) X1 X0
               grind)
            | (have i₁ := b8e3572 X1 X2 X1
               have i₂ := b8e3013 (M.op X1 X2) X0 X1
               grind)
            | exact superpose b8e3013 b8e3572
            | exact resolve b8e3572 b8e3013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3572
          have b8e45267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1958
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1958
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e1958
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1958
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1958 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1958
          have b8e45268 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by grind
          clear b8e45267
          have b8e45269 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e45268
               have r₂ := b8e21
               grind)
            | exact resolve b8e45268 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45268
          have b8e45270 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e45269
               grind)
            | exact superpose b8e45269 b8e14
            | exact resolve b8e14 b8e45269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45269
          have b8e45387 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e45270
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e45270
            | exact resolve b8e45270 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45270
          have b8e45394 : y = (M.op y x) := by
            first
            | (have r₁ := b8e45387
               have r₂ := b8e22
               grind)
            | exact resolve b8e45387 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45387
          have b8e45910 : (M.op x (M.op x x)) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b8e403 x y
               have i₂ := b8e45394
               grind)
            | exact superpose b8e45394 b8e403
            | exact resolve b8e403 b8e45394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e403
          have b8e45916 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e3013 x y X0
               have i₂ := b8e45394
               grind)
            | exact superpose b8e45394 b8e3013
            | exact resolve b8e3013 b8e45394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3013
          have b8e45935 : ∀ X0 : G, (M.op x x) = (M.op y (M.op X0 (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b8e14787 X0 y x
               have i₂ := b8e45394
               grind)
            | exact superpose b8e45394 b8e14787
            | exact resolve b8e14787 b8e45394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14787
          have b8e45945 : y = (M.op x x) := by
            first
            | (have i₁ := b8e45935 x
               have i₂ := b8e3574 x y
               grind)
            | exact superpose b8e3574 b8e45935
            | exact resolve b8e45935 b8e3574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3574 b8e45935
          have b8e45955 : (M.op x y) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b8e45910
               have i₂ := b8e45394
               grind)
            | exact superpose b8e45394 b8e45910
            | exact resolve b8e45910 b8e45394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45394 b8e45910
          have b8e45977 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e45955
               have i₂ := b8e45916 x
               grind)
            | exact superpose b8e45916 b8e45955
            | exact resolve b8e45955 b8e45916
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45916 b8e45955
          have b8e46432 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (σ x) (M.op (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b8e95 x X1 x
               have i₂ := b8e45945
               grind)
            | exact superpose b8e45945 b8e95
            | exact resolve b8e95 b8e45945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95
          have b8e46447 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e240 x x
               have i₂ := b8e45945
               grind)
            | exact superpose b8e45945 b8e240
            | exact resolve b8e240 b8e45945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e240
          have b8e46561 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) (σ (M.op x x))) := by
            intro X0 X1
            first
            | (have i₁ := b8e46432 X0 X1
               have i₂ := b8e823 x (M.op X1 (M.op (M.op X0 (σ x)) (σ y)))
               grind)
            | exact superpose b8e823 b8e46432
            | exact resolve b8e46432 b8e823
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e823 b8e46432
          have b8e46581 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e46561 X0 X1
               have i₂ := b8e45945
               grind)
            | exact superpose b8e45945 b8e46561
            | exact resolve b8e46561 b8e45945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45945 b8e46561
          have b8e46594 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e46581 X0 x
               have i₂ := b8e9274 (σ y) x (M.op X0 (σ x))
               grind)
            | exact superpose b8e9274 b8e46581
            | exact resolve b8e46581 b8e9274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9274 b8e46581
          have b8e46603 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e46594 x
               have i₂ := b8e46447 x
               grind)
            | exact superpose b8e46447 b8e46594
            | exact resolve b8e46594 b8e46447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46447 b8e46594
          have b8e46608 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e46603
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e46603
            | exact resolve b8e46603 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e46603
          have b8e46610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e46608
               have i₂ := b8e45977
               grind)
            | exact superpose b8e45977 b8e46608
            | exact resolve b8e46608 b8e45977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45977 b8e46608
          have b8e46611 : False := by grind
          exact b8e46611

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
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
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
               have i₂ := b5e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b5e40 (M.op x x)
               have i₂ := b5e13 x x x
               grind)
            | exact superpose b5e13 b5e40
            | exact resolve b5e40 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op x (M.op X0 X0)) y
               have i₂ := b5e40 X0
               grind)
            | exact superpose b5e40 b5e13
            | exact resolve b5e13 b5e40
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
          have b5e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e78 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e42 (σ X0) (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e42
            | exact resolve b5e42 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e82 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 X0 X0
               have i₂ := b5e42 X0 X0
               grind)
            | exact superpose b5e42 b5e13
            | exact resolve b5e13 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op x (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 (M.op X1 X0)
               have i₂ := b5e42 X1 X0
               grind)
            | exact superpose b5e42 b5e40
            | exact resolve b5e40 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e86 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e78 X0
               have i₂ := b5e31 (M.op X0 X0)
               grind)
            | exact superpose b5e31 b5e78
            | exact resolve b5e78 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e87 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e86 X0
               have i₂ := b5e42 X0 X0
               grind)
            | exact superpose b5e42 b5e86
            | exact resolve b5e86 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e120 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e13 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b5e41 X1 x x X0
               grind)
            | exact superpose b5e41 b5e13
            | exact resolve b5e13 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e591 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 x)) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e84 (M.op X0 x) (M.op X0 x)
               have i₂ := b5e13 (M.op X0 x) x X0
               grind)
            | exact superpose b5e13 b5e84
            | exact resolve b5e84 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e600 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e591 X0
               have i₂ := b5e42 X0 x
               grind)
            | exact superpose b5e42 b5e591
            | exact resolve b5e591 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e591
          have b5e675 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e40 (M.op X0 (M.op X0 X0))
               have i₂ := b5e120 X0 X0 X0
               grind)
            | exact superpose b5e120 b5e40
            | exact resolve b5e40 b5e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e120
          have b5e727 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e82 X0
               have i₂ := b5e675 X0
               grind)
            | exact superpose b5e675 b5e82
            | exact resolve b5e82 b5e675
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e675
          have b5e817 : y = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b5e727 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e727
            | exact resolve b5e727 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e727
          have b5e840 : y = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b5e817
               have i₂ := b5e600 y
               grind)
            | exact superpose b5e600 b5e817
            | exact resolve b5e817 b5e600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e600 b5e817
          have b5e841 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e840
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e840
            | exact resolve b5e840 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840
          have b5e874 : x = (M.op y y) := by
            first
            | (have i₁ := b5e44 x x
               have i₂ := b5e841
               grind)
            | exact superpose b5e841 b5e44
            | exact resolve b5e44 b5e841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e928 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e87 y
               have i₂ := b5e874
               grind)
            | exact superpose b5e874 b5e87
            | exact resolve b5e87 b5e874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e943 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e928
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e928
            | exact resolve b5e928 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e928
          have b5e3134 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e52 y x
               have i₂ := b5e943
               grind)
            | exact superpose b5e943 b5e52
            | (have j0 := b5e52 y x
               grind)
            | exact resolve b5e52 b5e943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e943
          have b5e3164 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e3134
               have r₂ := b5e24
               grind)
            | exact resolve b5e3134 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3134
          have b5e3175 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e3164
               have r₂ := b5e23
               grind)
            | exact resolve b5e3164 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3164
          have b5e3181 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e3175
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e3175
            | exact resolve b5e3175 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e3175
          have b5e3269 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e31 (M.op x x)
               have i₂ := b5e3181
               grind)
            | exact superpose b5e3181 b5e31
            | exact resolve b5e31 b5e3181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3181
          have b5e3301 : (σ (M.op y y)) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b5e3269
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e3269
            | exact resolve b5e3269 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e3269
          have b5e3312 : (σ (M.op x (M.op x x))) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e3301
               have i₂ := b5e42 x x
               grind)
            | exact superpose b5e42 b5e3301
            | exact resolve b5e3301 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e3301
          have b5e3317 : (σ x) = (σ (M.op x (M.op x x))) := by
            first
            | (have i₁ := b5e3312
               have i₂ := b5e874
               grind)
            | exact superpose b5e874 b5e3312
            | exact resolve b5e3312 b5e874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e874 b5e3312
          have b5e3322 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e3317
               have i₂ := b5e841
               grind)
            | exact superpose b5e841 b5e3317
            | exact resolve b5e3317 b5e841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e841 b5e3317
          have b5e3326 : False := by grind
          exact b5e3326
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b7e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 := by
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
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
               have i₂ := b7e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b7e27
          have b7e41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e37 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e37
            | exact resolve b7e37 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b7e41
          have b7e43 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e50 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e51 : y = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : y = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e64 : y = (M.op y x) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e79 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e13
            | exact resolve b7e13 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e109 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e35 (σ X0) (σ X0)
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e35
            | exact resolve b7e35 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e111 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e35 y x
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e35
            | exact resolve b7e35 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e116 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e109 X0
               have i₂ := b7e31 (M.op X0 X0)
               grind)
            | exact superpose b7e31 b7e109
            | exact resolve b7e109 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e118 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e116 X0
               have i₂ := b7e35 X0 X0
               grind)
            | exact superpose b7e35 b7e116
            | exact resolve b7e116 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116
          have b7e122 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 y X0 X1
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e13
            | exact resolve b7e13 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e150 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e13 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b7e34 X1 x x X0
               grind)
            | exact superpose b7e34 b7e13
            | exact resolve b7e13 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e151 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (σ x) (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b7e34 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e34 b7e33
            | exact resolve b7e33 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e154 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e151 X0 X1
               have i₂ := b7e35 X0 X1
               grind)
            | exact superpose b7e35 b7e151
            | exact resolve b7e151 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e252 : ∀ X0 : G, (σ X0) = (M.op x (M.op y (σ (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e79 (σ X0)
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e79
            | exact resolve b7e79 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e79
          have b7e585 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) = (M.op x (M.op y (σ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e252 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
               have i₂ := b7e34 (M.op X0 X1) X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b7e34 b7e252
            | exact resolve b7e252 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e600 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (M.op x (M.op y (σ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e585 X0 X1
               have i₂ := b7e35 X0 X1
               grind)
            | exact superpose b7e35 b7e585
            | exact resolve b7e585 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e585
          have b7e602 : ∀ X0 X1 : G, (σ (M.op (σ y) (M.op (σ x) (M.op X0 X1)))) = (M.op x (M.op y (σ (M.op X0 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e600 X0 X1
               have i₂ := b7e154 X0 X1
               grind)
            | exact superpose b7e154 b7e600
            | exact resolve b7e600 b7e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e600
          have b7e733 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op x (M.op y (σ X0))) := by
            intro X0
            first
            | (have i₁ := b7e252 (M.op X0 (M.op X0 X0))
               have i₂ := b7e150 X0 X0 X0
               grind)
            | exact superpose b7e150 b7e252
            | exact resolve b7e252 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e915 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e118 (M.op (τ X0) (τ X0))
               have i₂ := b7e42 X0
               grind)
            | exact superpose b7e42 b7e118
            | exact resolve b7e118 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e945 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e915 X0
               have i₂ := b7e35 (τ X0) (τ X0)
               grind)
            | exact superpose b7e35 b7e915
            | exact resolve b7e915 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e915
          have b7e960 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (M.op x (M.op y (σ (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e945 X0
               have i₂ := b7e733 (τ X0)
               grind)
            | exact superpose b7e733 b7e945
            | exact resolve b7e945 b7e733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e733 b7e945
          have b7e970 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b7e960 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e960
            | exact resolve b7e960 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e960
          have b7e978 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x (M.op y X0))) = (σ (M.op (σ y) (M.op (σ x) (M.op (τ X0) (τ X0))))) := by
            intro X0
            first
            | (have i₁ := b7e970 X0
               have i₂ := b7e154 (τ X0) (τ X0)
               grind)
            | exact superpose b7e154 b7e970
            | exact resolve b7e970 b7e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154 b7e970
          have b7e980 : ∀ X0 : G, (M.op x (M.op y (σ (M.op (τ X0) (τ X0))))) = (M.op (M.op X0 X0) (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b7e978 X0
               have i₂ := b7e602 (τ X0) (τ X0)
               grind)
            | exact superpose b7e602 b7e978
            | exact resolve b7e978 b7e602
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e602 b7e978
          have b7e981 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b7e980 X0
               have i₂ := b7e252 (τ X0)
               grind)
            | exact superpose b7e252 b7e980
            | exact resolve b7e980 b7e252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e252 b7e980
          have b7e982 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e981 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e981
            | exact resolve b7e981 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e981
          have b7e990 : x = (M.op (M.op x x) (M.op x y)) := by
            first
            | (have i₁ := b7e982 x
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e982
            | exact resolve b7e982 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e982
          have b7e1053 : y = (M.op x x) := by
            first
            | (have i₁ := b7e122 x x
               have i₂ := b7e990
               grind)
            | exact superpose b7e990 b7e122
            | exact resolve b7e122 b7e990
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122 b7e990
          have b7e1125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e118 x
               have i₂ := b7e1053
               grind)
            | exact superpose b7e1053 b7e118
            | exact resolve b7e118 b7e1053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118 b7e1053
          have b7e1135 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b7e1125
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1125
            | exact resolve b7e1125 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1125
          have b7e1146 : False := by grind
          exact b7e1146
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
               have i₂ := b8e13 X0 X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
               have i₂ := b8e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e63 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e33 (σ X0) (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e33
            | exact resolve b8e33 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X1 X0) X2 X3
               have i₂ := b8e33 X1 X0
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e63 X0
               have i₂ := b8e30 (M.op X0 X0)
               grind)
            | exact superpose b8e30 b8e63
            | exact resolve b8e63 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e63
          have b8e69 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e68 X0
               have i₂ := b8e33 X0 X0
               grind)
            | exact superpose b8e33 b8e68
            | exact resolve b8e68 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e68
          have b8e99 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b8e13 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
               have i₂ := b8e32 X1 x x X0
               grind)
            | exact superpose b8e32 b8e13
            | exact resolve b8e13 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e144 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 (σ X0) (σ X1)
               have i₂ := b8e55 X1 X0
               grind)
            | exact superpose b8e55 b8e17
            | (have j0 := b8e17 (σ X0) (σ X1)
               have j1 := b8e55 X1 X0
               grind)
            | (have r₁ := b8e17 (σ X1) (σ X0)
               have r₂ := b8e55 X0 X1
               grind)
            | exact resolve b8e17 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e147 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e144 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144
          have b8e148 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e147 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e148 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e148
            | (have j0 := b8e148 X0 X1
               grind)
            | exact resolve b8e148 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148
          have b8e420 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X0 (M.op X0 X0)) X1 X2
               have i₂ := b8e99 X0 X0 X0
               grind)
            | exact superpose b8e99 b8e13
            | exact resolve b8e13 b8e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e1352 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e67 X0 (M.op X1 X0) X2 X3
               have i₂ := b8e420 X0 X0 X1
               grind)
            | exact superpose b8e420 b8e67
            | exact resolve b8e67 b8e420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e420
          have b8e1367 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e1352 X0 X1 x x
               have i₂ := b8e67 X0 X0 x x
               grind)
            | exact superpose b8e67 b8e1352
            | exact resolve b8e1352 b8e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67 b8e1352
          have b8e4121 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e152 y x
               grind)
            | exact superpose b8e152 b8e20
            | (have j1 := b8e152 x y
               grind)
            | exact resolve b8e20 b8e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e152
          have b8e4171 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b8e4121
               have r₂ := b8e23
               grind)
            | exact resolve b8e4121 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4121
          have b8e33676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e4171
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e4171
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e4171
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e4171
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e4171 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4171
          have b8e33677 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by grind
          clear b8e33676
          have b8e33678 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e33677
               have r₂ := b8e21
               grind)
            | exact resolve b8e33677 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33677
          have b8e33679 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e33678
               grind)
            | exact superpose b8e33678 b8e14
            | exact resolve b8e14 b8e33678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33678
          have b8e33784 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e33679
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e33679
            | exact resolve b8e33679 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33679
          have b8e33794 : y = (M.op y x) := by
            first
            | (have r₁ := b8e33784
               have r₂ := b8e22
               grind)
            | exact resolve b8e33784 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33784
          have b8e33838 : (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b8e1367 x y
               have i₂ := b8e33794
               grind)
            | exact superpose b8e33794 b8e1367
            | exact resolve b8e1367 b8e33794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1367
          have b8e33882 : y = (M.op x x) := by
            first
            | (have i₁ := b8e33838
               have i₂ := b8e33794
               grind)
            | exact superpose b8e33794 b8e33838
            | exact resolve b8e33838 b8e33794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33794 b8e33838
          have b8e34440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e69 x
               have i₂ := b8e33882
               grind)
            | exact superpose b8e33882 b8e69
            | exact resolve b8e69 b8e33882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69 b8e33882
          have b8e34635 : False := by grind
          exact b8e34635

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e182 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 x y
               grind)
            | exact superpose b4e48 b4e20
            | (have j1 := b4e48 x y
               grind)
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e187 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b4e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e191 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e182
               have r₂ := b4e23
               grind)
            | exact resolve b4e182 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182
          have b4e3251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e191
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e191
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e191
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e191
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e191 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191
          have b4e3252 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b4e3251
          have b4e3253 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e3252
               have r₂ := b4e21
               grind)
            | exact resolve b4e3252 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3252
          have b4e9562 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3253
               grind)
            | exact superpose b4e3253 b4e20
            | exact resolve b4e20 b4e3253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9564 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e3253
               grind)
            | exact superpose b4e3253 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e3253
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e3253
               grind)
            | exact resolve b4e17 b4e3253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3253
          have b4e9595 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e9564
          have b4e9597 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e9595
               have r₂ := b4e23
               grind)
            | exact resolve b4e9595 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9595
          have b4e9599 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e9597
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e9597
            | exact resolve b4e9597 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9597
          have b4e9846 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e9599
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e9599
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e9599 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9599
          have b4e9879 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b4e9846
          have b4e9897 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e9879
               have r₂ := b4e9562
               grind)
            | exact resolve b4e9879 b4e9562
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9562 b4e9879
          have b4e9901 : y = (M.op x y) := by
            first
            | (have r₁ := b4e9897
               have r₂ := b4e21
               grind)
            | exact resolve b4e9897 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9897
          have b4e9942 : y ≠ y ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e9901
               grind)
            | exact superpose b4e9901 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e9901
               grind)
            | exact resolve b4e17 b4e9901
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9972 : x = y ∨ y = (k y x) := by grind
          clear b4e9942
          have b4e9974 : y = (k y x) := by
            first
            | (have r₁ := b4e9972
               have r₂ := b4e21
               grind)
            | exact resolve b4e9972 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9972
          have b4e10098 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e187 x y
               have i₂ := b4e9974
               grind)
            | exact superpose b4e9974 b4e187
            | (have j0 := b4e187 x y
               grind)
            | exact resolve b4e187 b4e9974
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e187 b4e9974
          have b4e10101 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b4e10098
          have b4e10103 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e10101
               have r₂ := b4e23
               grind)
            | exact resolve b4e10101 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10101
          have b4e11705 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e10103
               grind)
            | exact superpose b4e10103 b4e20
            | exact resolve b4e20 b4e10103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10103
          have b4e11741 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e11705
               have i₂ := b4e9901
               grind)
            | exact superpose b4e9901 b4e11705
            | exact resolve b4e11705 b4e9901
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9901 b4e11705
          have b4e11742 : False := by grind
          exact b4e11742
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
          have b5e36 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e39 : x = y ∨ x = (k x y) := by grind
          clear b5e36
          have b5e40 : x = (k x y) := by
            first
            | (have r₁ := b5e39
               have r₂ := b5e21
               grind)
            | exact resolve b5e39 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e157 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e4844 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e157 y x
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e157
            | (have j0 := b5e157 y x
               grind)
            | exact resolve b5e157 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e157
          have b5e4847 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e4844
          have b5e4850 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e4847
               have r₂ := b5e24
               grind)
            | exact resolve b5e4847 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4847
          have b5e4854 : False := by grind
          exact b5e4854
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
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ x) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ x)) := by
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
          have b7e50 : x = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : x = (M.op y x) ∨ x = y := by grind
          clear b7e60
          have b7e63 : x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e65 : False := by grind
          exact b7e65
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e130 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e139 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e130
               have r₂ := b8e23
               grind)
            | exact resolve b8e130 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e1687 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e139
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e139
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e139
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e139
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e139 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1688 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e1687
          have b8e1689 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e1688
               have r₂ := b8e21
               grind)
            | exact resolve b8e1688 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1688
          have b8e2052 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1689
               grind)
            | exact superpose b8e1689 b8e20
            | exact resolve b8e20 b8e1689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2054 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e1689
               grind)
            | exact superpose b8e1689 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e1689
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1689
               grind)
            | exact resolve b8e17 b8e1689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1689
          have b8e2070 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e2054
          have b8e2071 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e2070
               have r₂ := b8e23
               grind)
            | exact resolve b8e2070 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2070
          have b8e2073 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e2071
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e2071
            | exact resolve b8e2071 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2071
          have b8e2697 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e2073
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e2073
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e2073 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2073
          have b8e2720 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e2697
          have b8e2735 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e2720
               have r₂ := b8e2052
               grind)
            | exact resolve b8e2720 b8e2052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2052 b8e2720
          have b8e2736 : y = (M.op x y) := by
            first
            | (have r₁ := b8e2735
               have r₂ := b8e21
               grind)
            | exact resolve b8e2735 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2735
          have b8e2944 : y ≠ y ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e2736
               grind)
            | exact superpose b8e2736 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e2736
               grind)
            | exact resolve b8e17 b8e2736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2964 : x = y ∨ y = (k y x) := by grind
          clear b8e2944
          have b8e2965 : y = (k y x) := by
            first
            | (have r₁ := b8e2964
               have r₂ := b8e21
               grind)
            | exact resolve b8e2964 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2964
          have b8e3039 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e139
               have i₂ := b8e2965
               grind)
            | exact superpose b8e2965 b8e139
            | exact resolve b8e139 b8e2965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139 b8e2965
          have b8e3043 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e3039
               have i₂ := b8e2736
               grind)
            | exact superpose b8e2736 b8e3039
            | exact resolve b8e3039 b8e2736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3039
          have b8e3044 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e3043
          have b8e3110 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3044
               grind)
            | exact superpose b8e3044 b8e20
            | exact resolve b8e20 b8e3044
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3044
          have b8e3136 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e3110
               have i₂ := b8e2736
               grind)
            | exact superpose b8e2736 b8e3110
            | exact resolve b8e3110 b8e2736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2736 b8e3110
          have b8e3137 : False := by grind
          exact b8e3137
